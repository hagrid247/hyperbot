#!/usr/bin/env python3
"""Zero-Privilege Hardened Builder Agent (Production Hardened & Token-Optimized Edition)."""

import argparse
import ast
import hashlib
import os
import re
import shutil
import subprocess
import sys
import tempfile
import time
import uuid
from dataclasses import dataclass
from typing import Optional, Set, Tuple

try:
    from google import genai
    from google.genai import types
except ImportError:
    genai = None
    types = None

@dataclass
class CheckResult:
    success: bool
    error_type: Optional[str] = None
    message: str = ""
    error_line: Optional[int] = None
    culprit_file: Optional[str] = None
    missing_symbol: Optional[str] = None

class CostTracker:
    """Seuraa arvioituja API-tokenikustannuksia (Gemini 3.8 Flash)."""
    RATES = {"input": 0.10 / 1_000_000, "output": 0.40 / 1_000_000}

    def __init__(self, budget_eur: float = 2.0):
        self.budget_eur = budget_eur
        self.total_spent_eur = 0.0

    def add_usage(self, prompt_tokens: int, candidates_tokens: int) -> float:
        call_cost = (prompt_tokens * self.RATES["input"]) + (candidates_tokens * self.RATES["output"])
        self.total_spent_eur += call_cost
        return call_cost

    def has_budget(self) -> bool:
        return self.total_spent_eur < self.budget_eur

class AntiCheat(ast.NodeVisitor):
    """Estää triviaalit vakionpalautukset; huomioi async-funktiot ja monipuoliset argumentit."""
    def __init__(self):
        self.cheated = False
        self.func = ""

    def _check_func(self, node: ast.AST):
        if not isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
            return
        all_args = (
            node.args.args +
            node.args.kwonlyargs +
            ([node.args.vararg] if node.args.vararg else []) +
            ([node.args.kwarg] if node.args.kwarg else [])
        )
        real_args = [a.arg for a in all_args if a and a.arg not in ("self", "cls")]
        if real_args:
            body = [n for n in node.body if not isinstance(n, (ast.Expr, ast.Pass))]
            if len(body) == 1 and isinstance(body[0], ast.Return) and isinstance(body[0].value, ast.Constant):
                self.cheated = True
                self.func = node.name

    def visit_FunctionDef(self, node: ast.FunctionDef):
        self._check_func(node)
        self.generic_visit(node)

    def visit_AsyncFunctionDef(self, node: ast.AsyncFunctionDef):
        self._check_func(node)
        self.generic_visit(node)

def verify_ast_static(filepath: str) -> Tuple[bool, str]:
    try:
        with open(filepath, "r", encoding="utf-8-sig", errors="replace") as f:
            code = f.read()
        tree = ast.parse(code)
    except SyntaxError as e:
        return False, f"SyntaxError rivillä {e.lineno}: {e.msg}"
    except Exception as e:
        return False, f"AST-luku epäonnistui: {str(e)}"

    checker = AntiCheat()
    checker.visit(tree)
    if checker.cheated:
        return False, f"Anti-Cheat: Funktio '{checker.func}' palauttaa pelkän vakion."
    return True, ""

def extract_code_slice(code: str, err_line: Optional[int], context_lines: int = 25) -> Tuple[str, bool, Optional[Tuple[int, int]]]:
    """Eristää virhekohdan funktion tai liukuvan ikkunan ja palauttaa (koodi, onko_leike, (alku, loppu))."""
    if not err_line:
        return code, False, None

    lines = code.splitlines()
    if not (1 <= err_line <= len(lines)):
        return code, False, None

    try:
        tree = ast.parse(code)
        for node in ast.walk(tree):
            if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef)):
                end_lineno = getattr(node, "end_lineno", None)
                if end_lineno and node.lineno <= err_line <= end_lineno:
                    start_idx = node.lineno - 1
                    end_idx = end_lineno
                    return "\n".join(lines[start_idx:end_idx]), True, (start_idx, end_idx)
    except Exception:
        pass

    start_idx = max(0, err_line - context_lines - 1)
    end_idx = min(len(lines), err_line + context_lines)
    return "\n".join(lines[start_idx:end_idx]), True, (start_idx, end_idx)

def clean_traceback(raw: str, root_dir: str, default_target: str) -> Tuple[str, Optional[int], Optional[str], str, Optional[str]]:
    lines = raw.splitlines()
    err_line, culprit, err_type, missing_sym = None, None, "RUNTIME_ERROR", None

    for l in lines:
        if "NotImplementedError" in l:
            err_type = "NOT_IMPLEMENTED"
        m_attr = re.search(r"module ['\"](.*?)['\"] has no attribute ['\"](.*?)['\"]", l)
        if m_attr:
            err_type, missing_sym = "MISSING_ATTRIBUTE", m_attr.group(2)
            mod_file = m_attr.group(1).replace(".", os.sep) + ".py"
            cand = os.path.normpath(os.path.join(root_dir, mod_file))
            if os.path.isfile(cand):
                culprit = cand

        m_line = re.search(r'File\s+"(.*?)",\s+line\s+(\d+)', l)
        if m_line:
            path = m_line.group(1)
            if "/tmp/run/" in path:
                rel_path = path.split("/tmp/run/", 1)[1]
                cand = os.path.normpath(os.path.join(root_dir, rel_path))
                if os.path.isfile(cand):
                    culprit, err_line = cand, int(m_line.group(2))
            elif not any(s in path for s in [".venv", "site-packages", "/usr/local/lib"]):
                cand = os.path.normpath(os.path.join(root_dir, os.path.basename(path)))
                if os.path.isfile(cand):
                    culprit, err_line = cand, int(m_line.group(2))

    return "\n".join(lines[-10:]), err_line, culprit or default_target, err_type, missing_sym

def execute_sandboxed(
    target: str,
    workspace_root: Optional[str] = None,
    cmd: Optional[str] = None,
    img: str = "python:3.11-alpine"
) -> CheckResult:
    abs_t = os.path.abspath(target)
    root_dir = os.path.abspath(workspace_root) if workspace_root else os.path.dirname(abs_t)
    rel_target = os.path.relpath(abs_t, root_dir)

    ok, msg = verify_ast_static(abs_t)
    if not ok:
        return CheckResult(False, "PRECHECK_FAIL", msg, culprit_file=abs_t)

    container_name = f"sandbox_{uuid.uuid4().hex[:8]}"
    run_cmd = cmd or f"python {rel_target}"

    current_uid = os.getuid() if hasattr(os, "getuid") else 1000
    current_gid = os.getgid() if hasattr(os, "getgid") else 1000

    docker_cmd = [
        "docker", "run",
        "--name", container_name,
        "--rm",
        "--network", "none",
        "--read-only",
        "--cap-drop=ALL",
        "--security-opt", "no-new-privileges:true",
        f"--user={current_uid}:{current_gid}",
        "--memory=256m",
        "--cpus=1.0",
        "--pids-limit=32",
        "--tmpfs", "/tmp/run:rw,nosuid,size=64m,mode=1777",
        "-v", f"{root_dir}:/repo:ro",
        img,
        "/bin/sh", "-c", 'cp -r /repo/. /tmp/run/ && cd /tmp/run && exec "$@"',
        "--", "sh", "-c", run_cmd
    ]

    try:
        proc = subprocess.run(docker_cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True, timeout=20)
        if proc.returncode != 0:
            err, line, c_file, e_type, sym = clean_traceback(proc.stderr or proc.stdout, root_dir, abs_t)
            return CheckResult(False, e_type, err, line, c_file, sym)
        return CheckResult(True, message="Testit läpäisty.")
    except subprocess.TimeoutExpired:
        return CheckResult(False, "TIMEOUT", "Aikaraja ylittyi (20s).", culprit_file=abs_t)
    finally:
        subprocess.run(["docker", "rm", "-f", container_name], stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)

def apply_patch(src: str, patch: str, line_range: Optional[Tuple[int, int]] = None) -> Optional[str]:
    clean_patch = patch.strip()
    fence_match = re.search(r"```(?:diff|python)?\s*\n(.*?)\n```", clean_patch, re.DOTALL)
    if fence_match:
        clean_patch = fence_match.group(1).strip()

    m = re.search(r"<<<<<<<\s*SEARCH\r?\n(.*?)\r?\n=======\r?\n(.*?)\r?\n>>>>>>>\s*REPLACE", clean_patch, re.DOTALL)
    if not m:
        return None

    s_clean = re.sub(r"^\s*(?:->|HDR)?\s*\d+\s*\|\s*", "", m.group(1), flags=re.MULTILINE).replace("\r\n", "\n")
    r_clean = re.sub(r"^\s*(?:->|HDR)?\s*\d+\s*\|\s*", "", m.group(2), flags=re.MULTILINE).replace("\r\n", "\n")
    src_normalized = src.replace("\r\n", "\n")

    # 1. Kohdistus leikkauksen rivialueelle
    if line_range:
        lines = src_normalized.splitlines(keepends=True)
        start_idx, end_idx = line_range
        target_chunk = "".join(lines[start_idx:end_idx])
        if s_clean in target_chunk:
            new_chunk = target_chunk.replace(s_clean, r_clean, 1)
            return "".join(lines[:start_idx]) + new_chunk + "".join(lines[end_idx:])

    # 2. Tarkka haku koko tiedostosta
    if s_clean in src_normalized:
        return src_normalized.replace(s_clean, r_clean, 1)

    # 3. Whitespace-tolerantti sovitus
    s_norm = "\n".join(line.strip() for line in s_clean.splitlines() if line.strip())
    src_lines = src_normalized.splitlines()
    for i in range(len(src_lines)):
        for j in range(i + 1, min(i + len(s_clean.splitlines()) + 3, len(src_lines) + 1)):
            chunk = "\n".join(line.strip() for line in src_lines[i:j] if line.strip())
            if chunk == s_norm:
                prefix = "\n".join(src_lines[:i])
                suffix = "\n".join(src_lines[j:])
                parts = [p for p in [prefix, r_clean, suffix] if p]
                return "\n".join(parts)
    return None

def is_protected_file(filepath: str) -> bool:
    norm = os.path.normpath(filepath).lower()
    base = os.path.basename(norm)
    path_parts = norm.split(os.sep)
    return (
        base.startswith("test_") or
        base.endswith("_test.py") or
        "holdout" in base or
        base.startswith("conftest") or
        any(p in path_parts for p in ("tests", "fixtures"))
    )

SYSTEM_REPAIR_INSTRUCTION = (
    "You are an automated code repair specialist. Respond ONLY with a single search/replace block. "
    "Never write conversational filler, markdown explanations, or thoughts. "
    "Output must exactly follow this schema:\n"
    "<<<<<<< SEARCH\n"
    "[exact existing code]\n"
    "=======\n"
    "[exact replacement code]\n"
    ">>>>>>> REPLACE"
)

def build_compact_user_prompt(
    target_name: str,
    code_snippet: str,
    res: CheckResult,
    is_slice: bool = False,
    decompose: bool = False,
    human_hint: Optional[str] = None
) -> str:
    parts = [f"TARGET: {target_name}", f"ERROR: {res.error_type}"]
    if res.error_line:
        parts.append(f"LINE: {res.error_line}")
    if res.missing_symbol:
        parts.append(f"MISSING SYMBOL: {res.missing_symbol}")
    if is_slice:
        parts.append("SCOPE: Fix strictly within the provided code slice.")
    if decompose:
        parts.append("DIRECTIVE: Decompose complex logic into small private helper functions.")
    if human_hint:
        parts.append(f"SUPERVISOR DIRECTIVE: {human_hint}")

    parts.append(f"\nLOG:\n{res.message.strip()}")
    parts.append(f"\nCODE:\n{code_snippet}")
    return "\n".join(parts)

def heal(
    target: str,
    res: CheckResult,
    seen: Set[Tuple[str, str]],
    tracker: CostTracker,
    workspace_root: str,
    attempt: int = 1,
    human_hint: Optional[str] = None
) -> Tuple[bool, str]:
    MODEL_NAME = "gemini-3.8-flash"

    if genai is None or types is None:
        return False, "google-genai -kirjasto puuttuu. Asenna se: pip install google-genai"

    if is_protected_file(target):
        return False, f"Tiedosto '{os.path.basename(target)}' on suojattu testitiedosto. Muokkaus estetty."

    if not tracker.has_budget():
        return False, f"Budjettiraja ({tracker.budget_eur:.2f} €) täynnä. Korjaus keskeytetään."

    api_key = os.environ.get("GEMINI_API_KEY") or os.environ.get("GOOGLE_API_KEY")
    if not api_key:
        return False, "GEMINI_API_KEY puuttuu ympäristömuuttujista."

    with open(target, "r", encoding="utf-8-sig") as f:
        full_code = f.read()

    decompose = (attempt == 3)
    line_range = None
    if attempt <= 2 and res.error_line:
        code_snippet, is_slice, line_range = extract_code_slice(full_code, res.error_line)
    else:
        code_snippet, is_slice = full_code, False

    user_prompt = build_compact_user_prompt(
        os.path.basename(target),
        code_snippet,
        res,
        is_slice=is_slice,
        decompose=decompose,
        human_hint=human_hint
    )
    client = genai.Client(api_key=api_key)

    resp = None
    for api_try in range(2):
        try:
            resp = client.models.generate_content(
                model=MODEL_NAME,
                contents=user_prompt,
                config=types.GenerateContentConfig(
                    system_instruction=SYSTEM_REPAIR_INSTRUCTION,
                    temperature=0.1,
                    max_output_tokens=1024
                )
            )
            break
        except Exception as e:
            err_msg = str(e).lower()
            if "429" in err_msg or "resource_exhausted" in err_msg or "quota" in err_msg:
                if api_try == 0:
                    print("  [429 Quota Exceeded]: Kiintiö täynnä. Odotetaan 15s...")
                    time.sleep(15)
                    continue
                return False, "429 Quota Exceeded: Kiintiö täynnä. Keskeytetään turvallisesti."
            return False, f"API-virhe: {e}"

    if not resp or not resp.text:
        return False, "LLM ei palauttanut vastausta."

    if hasattr(resp, "usage_metadata") and resp.usage_metadata:
        in_tok = resp.usage_metadata.prompt_token_count or 0
        out_tok = resp.usage_metadata.candidates_token_count or 0
        call_cost = tracker.add_usage(in_tok, out_tok)
        tok_mode = "Osaleike" if is_slice else "Koko koodi"
        print(f"  [{tok_mode} | In: {in_tok} tok, Out: {out_tok} tok | +{call_cost:.5f} € | Yht: {tracker.total_spent_eur:.4f} €]")

    new_code = apply_patch(full_code, resp.text, line_range=line_range)
    if not new_code or new_code == full_code:
        return False, "Patch ei kohdistunut tai koodi ei muuttunut."

    rel_target = os.path.relpath(target, workspace_root)
    sha = hashlib.sha256(new_code.encode()).hexdigest()
    state_key = (rel_target, sha)
    if state_key in seen:
        return False, f"Oskillaatio havaittu tiedostolle '{rel_target}' (tila on jo kokeiltu)."
    seen.add(state_key)

    with open(target, "w", encoding="utf-8") as f:
        f.write(new_code)
    return True, "Muutos tallennettu varjotyötilaan."

def run_loop_in_shadow(
    shadow_target: str,
    shadow_root: str,
    test_cmd: Optional[str],
    holdout_cmd: Optional[str],
    img: str,
    tracker: CostTracker
) -> bool:
    seen_states: Set[Tuple[str, str]] = set()
    for root, _, files in os.walk(shadow_root):
        for f in files:
            if f.endswith(".py"):
                p = os.path.join(root, f)
                try:
                    with open(p, "rb") as fp:
                        rel = os.path.relpath(p, shadow_root)
                        seen_states.add((rel, hashlib.sha256(fp.read()).hexdigest()))
                except Exception:
                    pass

    for attempt in range(1, 4):
        res = execute_sandboxed(shadow_target, workspace_root=shadow_root, cmd=test_cmd, img=img)
        if res.success:
            if holdout_cmd:
                holdout_res = execute_sandboxed(shadow_target, workspace_root=shadow_root, cmd=holdout_cmd, img=img)
                if not holdout_res.success:
                    res = CheckResult(False, "HOLDOUT_FAIL", f"Piilotettu testi epäonnistui:\n{holdout_res.message}")
                else:
                    print(f"Kaikki testit läpäisty yrityksellä {attempt} (Gemini 3.8 Flash).")
                    return True
            else:
                print(f"Testit läpäisty yrityksellä {attempt} (Gemini 3.8 Flash).")
                return True

        culprit = res.culprit_file if (res.culprit_file and os.path.isfile(res.culprit_file)) else shadow_target
        mode_str = "Apufunktioiden pilkonta" if attempt == 3 else "Täsmäkorjaus"
        print(f"[{attempt}/4] Virhe ({res.error_type}) tiedostossa {os.path.basename(culprit)}. Tila: {mode_str}...")

        ok, msg = heal(culprit, res, seen_states, tracker, workspace_root=shadow_root, attempt=attempt)
        if not ok:
            print(f"  Varoitus: {msg}")
            if "Budjettiraja" in msg or "429" in msg:
                return False

    res = execute_sandboxed(shadow_target, workspace_root=shadow_root, cmd=test_cmd, img=img)
    if res.success and (not holdout_cmd or execute_sandboxed(shadow_target, workspace_root=shadow_root, cmd=holdout_cmd, img=img).success):
        return True

    # HUMAN-IN-THE-LOOP (Yritys 4 / TTY-suojattu)
    print("\n" + "=" * 65)
    print("HUMAN-IN-THE-LOOP: Flash tarvitsee ihmisvalvojan ohjausta.")
    print(f"Kohdetiedosto: {os.path.basename(res.culprit_file or shadow_target)}")
    print(f"Viimeisin virhe: {res.error_type}")
    if res.message:
        print(f"Diagnostiikka:\n{res.message.strip()[-300:]}")
    print("=" * 65)

    user_hint = ""
    if sys.stdin.isatty():
        try:
            user_hint = input("\nAnna vihje tai ratkaisuohje Flashille (tai paina Enter peruuttaaksesi): ").strip()
        except (EOFError, KeyboardInterrupt):
            user_hint = ""
    else:
        print("\nEi interaktiivista päätettä (CI/CD havaittu) - ohitetaan ihmisvaihe.")

    if user_hint:
        print(f"\n[4/4] Suoritetaan viimeinen korjaus käyttäjän vihjeellä...")
        culprit = res.culprit_file if (res.culprit_file and os.path.isfile(res.culprit_file)) else shadow_target
        ok, msg = heal(culprit, res, seen_states, tracker, workspace_root=shadow_root, attempt=4, human_hint=user_hint)
        if ok:
            final_res = execute_sandboxed(shadow_target, workspace_root=shadow_root, cmd=test_cmd, img=img)
            if final_res.success and (not holdout_cmd or execute_sandboxed(shadow_target, workspace_root=shadow_root, cmd=holdout_cmd, img=img).success):
                print("Hienoa! Testit läpäisty käyttäjän vihjeen avulla.")
                return True

    return False

def run_workspace(
    target: str,
    test_cmd: Optional[str] = None,
    holdout_cmd: Optional[str] = None,
    img: str = "python:3.11-alpine",
    budget: float = 2.0
) -> bool:
    orig_target = os.path.abspath(target)
    orig_dir = os.path.dirname(orig_target)
    rel_file = os.path.relpath(orig_target, orig_dir)

    ignore_patterns = shutil.ignore_patterns(
        ".git", ".venv", "venv", "env", "__pycache__",
        ".pytest_cache", ".ruff_cache", ".mypy_cache",
        "node_modules", "*.pyc", "*.tmp"
    )

    tracker = CostTracker(budget_eur=budget)

    with tempfile.TemporaryDirectory(prefix="agent_shadow_") as shadow_dir:
        print(f"Alustetaan varjotyötila: {shadow_dir}")
        shutil.copytree(orig_dir, shadow_dir, dirs_exist_ok=True, ignore=ignore_patterns)

        shadow_target = os.path.join(shadow_dir, rel_file)
        success = False
        try:
            success = run_loop_in_shadow(
                shadow_target=shadow_target,
                shadow_root=shadow_dir,
                test_cmd=test_cmd,
                holdout_cmd=holdout_cmd,
                img=img,
                tracker=tracker
            )
        except KeyboardInterrupt:
            print("\n\nKäyttäjä keskeytti suorituksen (Ctrl+C).")

        if success:
            print("\n" + "=" * 65)
            print("KAIKKI TESTIT HYVÄKSYTTY!")
            print("Synkronoidaan toimivat muutokset alkuperäiseen kansioon...")
            shutil.copytree(shadow_dir, orig_dir, dirs_exist_ok=True, ignore=ignore_patterns)
            print("Valmis. Projektisi on päivitetty onnistuneesti.")
            print(f"Kokonaiskulu: {tracker.total_spent_eur:.5f} € / {tracker.budget_eur:.2f} €")
            print("=" * 65)
            return True
        else:
            print("\n" + "=" * 65)
            print("SUORITUS EPÄONNISTUI TAI KESKEYTETTIIN.")
            print("Varjotyötila heitetään roskiin. Alkuperäinen koodikantasi on 100 % koskematon.")
            print(f"Kokonaiskulu: {tracker.total_spent_eur:.5f} €")
            print("=" * 65)
            return False

if __name__ == "__main__":
    p = argparse.ArgumentParser(description="Zero-Privilege Hardened Builder Agent (Production Hardened & Token-Optimized)")
    p.add_argument("target", help="Korjattava päätiedosto")
    p.add_argument("--test-cmd", default=None, help="Yksikkötestikomento")
    p.add_argument("--holdout-cmd", default=None, help="Salattu holdout-testi")
    p.add_argument("--image", default="python:3.11-alpine", help="Docker-ajoympäristö")
    p.add_argument("--budget", type=float, default=2.0, help="Budjettikatto euroina (oletus: 2.0 €)")
    args = p.parse_args()

    success = run_workspace(args.target, args.test_cmd, args.holdout_cmd, args.image, args.budget)
    sys.exit(0 if success else 1)

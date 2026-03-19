#!/usr/bin/env python3
from __future__ import annotations
"""
LLM benchmark: can the model recover stripped essential assertions?

For each problem, the LLM receives verified code with all essential assertions
removed and must add assertions to make dafny verify pass again.

Logs everything: prompt, full LLM output (including thinking tokens),
dafny output, timing, token counts, per-attempt details.

Designed to run on Leonardo with SGLang or llama.cpp backends.

Usage:
    # Run all problems against SGLang
    python3 run_benchmark.py --inputs-dir ./inputs --backend sglang --url http://127.0.0.1:8000

    # Run all problems against llama.cpp
    python3 run_benchmark.py --inputs-dir ./inputs --backend llama --url http://127.0.0.1:8080

    # Run specific problems
    python3 run_benchmark.py --inputs-dir ./inputs --names 0000_1013_A 0003_1028_A

    # Parallel (multiple problems at once — use with SGLang for batching)
    python3 run_benchmark.py --inputs-dir ./inputs --backend sglang --workers 8
"""

import argparse
import asyncio
import json
import os
import re
import subprocess
import sys
import time
from datetime import datetime
from pathlib import Path


# ---------------------------------------------------------------------------
# Config
# ---------------------------------------------------------------------------

DAFNY = os.environ.get("DOTNET8", os.environ.get("DOTNET", "dotnet"))
DAFNY_DLL = os.environ.get("DAFNY_DLL", "Dafny.dll")
Z3_PATH = os.environ.get("Z3_PATH", None)
TIMEOUT_PER_PROBLEM = 500  # seconds
MAX_TOKENS = 16384
VERIFY_TIMEOUT = 60  # seconds per dafny verify call


# ---------------------------------------------------------------------------
# LLM backends
# ---------------------------------------------------------------------------

SYSTEM_MSG = "You are a Dafny verification expert. Output only code, no explanations."

# gpt-oss chat template (from llama.cpp log)
GPT_OSS_TEMPLATE = (
    "<|start|>system<|message|>{system}<|end|>"
    "<|start|>user<|message|>{user}<|end|>"
    "<|start|>assistant<|channel|>final<|message|>"
)


def _format_chat(prompt: str) -> str:
    """Apply gpt-oss chat template to a prompt."""
    return GPT_OSS_TEMPLATE.format(system=SYSTEM_MSG, user=prompt)


def call_sglang(url: str, prompt: str, max_tokens: int = MAX_TOKENS,
                temperature: float = 0.7) -> dict:
    """Call SGLang /generate endpoint with manual chat template."""
    import urllib.request

    formatted = _format_chat(prompt)
    payload = json.dumps({
        "text": formatted,
        "sampling_params": {
            "max_new_tokens": max_tokens,
            "temperature": temperature,
            "stop": ["</DAFNY_CODE>", "<|end|>"],
        },
    }).encode("utf-8")

    req = urllib.request.Request(
        f"{url}/generate",
        data=payload,
        headers={"Content-Type": "application/json"},
    )

    t0 = time.perf_counter()
    try:
        with urllib.request.urlopen(req, timeout=600) as resp:
            result = json.loads(resp.read().decode("utf-8"))
    except urllib.error.HTTPError as e:
        body = e.read().decode("utf-8", errors="replace")[:500]
        return {"text": "", "tokens": 0, "time": 0, "error": f"HTTP {e.code}: {body}"}
    except Exception as e:
        return {"text": "", "tokens": 0, "time": 0, "error": str(e)}

    elapsed = time.perf_counter() - t0
    text = result.get("text", "")
    meta = result.get("meta_info", {})

    return {
        "text": text,
        "tokens": meta.get("completion_tokens", 0),
        "prompt_tokens": meta.get("prompt_tokens", 0),
        "time": round(elapsed, 2),
        "raw": result,
    }


def call_llama(url: str, prompt: str, max_tokens: int = MAX_TOKENS,
               temperature: float = 0.7) -> dict:
    """Call llama.cpp /v1/chat/completions endpoint."""
    import urllib.request

    payload = json.dumps({
        "model": "gpt-oss",
        "messages": [
            {"role": "system", "content": SYSTEM_MSG},
            {"role": "user", "content": prompt},
        ],
        "max_tokens": max_tokens,
        "temperature": temperature,
        "stop": ["</DAFNY_CODE>"],
    }).encode("utf-8")

    req = urllib.request.Request(
        f"{url}/v1/chat/completions",
        data=payload,
        headers={"Content-Type": "application/json"},
    )

    t0 = time.perf_counter()
    try:
        with urllib.request.urlopen(req, timeout=600) as resp:
            result = json.loads(resp.read().decode("utf-8"))
    except urllib.error.HTTPError as e:
        body = e.read().decode("utf-8", errors="replace")[:500]
        return {"text": "", "tokens": 0, "time": 0, "error": f"HTTP {e.code}: {body}"}
    except Exception as e:
        return {"text": "", "tokens": 0, "time": 0, "error": str(e)}

    elapsed = time.perf_counter() - t0

    choices = result.get("choices", [])
    text = choices[0].get("message", {}).get("content", "") if choices else ""
    usage = result.get("usage", {})

    return {
        "text": text,
        "tokens": usage.get("completion_tokens", 0),
        "prompt_tokens": usage.get("prompt_tokens", 0),
        "time": round(elapsed, 2),
        "raw": result,
    }


# ---------------------------------------------------------------------------
# Code extraction
# ---------------------------------------------------------------------------

def extract_code(response: str) -> str | None:
    """Extract Dafny code from LLM response."""
    # Strategy 1: <DAFNY_CODE> tags
    for pattern in [
        r'<DAFNY_CODE>\s*(.*?)(?:</DAFNY_CODE>|$)',
        r'<code>\s*(.*?)(?:</code>|$)',
        r'<dafny>\s*(.*?)(?:</dafny>|$)',
    ]:
        m = re.search(pattern, response, re.DOTALL | re.IGNORECASE)
        if m:
            return m.group(1).strip()

    # Strategy 2: Markdown
    for pattern in [r'```dafny\s*(.*?)\s*```', r'```\s*(.*?)\s*```']:
        m = re.search(pattern, response, re.DOTALL)
        if m:
            return m.group(1).strip()

    # Strategy 3: Find from first 'method' or 'ghost' or 'predicate'
    m = re.search(r'((?:ghost\s+)?(?:method|function|predicate)\s+\w+.*)', response, re.DOTALL)
    if m:
        return m.group(1).strip()

    return None


# ---------------------------------------------------------------------------
# Dafny verification + spec comparison via AST mapping
# ---------------------------------------------------------------------------

def extract_spec_from_ast(ast: dict) -> dict:
    """Extract formal spec from AST mapping: functions, method signatures, body."""
    spec = {}
    spec["functions"] = sorted(
        [f["dafnyName"] for f in ast.get("functions", [])]
    )
    methods = []
    for m in ast.get("methods", []):
        methods.append({
            "name": m["name"],
            "requires": [r["text"] for r in m.get("requires", [])],
            "ensures": [e["text"] for e in m.get("ensures", [])],
            "invariants": [inv["text"] for inv in m.get("invariants", [])],
            "bodyStatements": m.get("bodyStatements", []),
        })
    spec["methods"] = methods
    return spec


def _normalize_stmt(s: dict) -> str:
    """Normalize a body statement to a comparable string (type + text + children)."""
    parts = [s.get("type", ""), s.get("text", "") or ""]
    for child in s.get("children") or []:
        parts.append(_normalize_stmt(child))
    return "|".join(parts)


def _body_matches(original: list, candidate: list) -> tuple[bool, str]:
    """Check that method body statements are identical (excluding asserts).

    The AST serializer already excludes assert/assume statements, so
    the remaining body tree must be exactly the same. Any extra variable
    declarations, changed assignments, modified control flow, etc. are
    rejected.
    """
    orig_normalized = [_normalize_stmt(s) for s in original]
    cand_normalized = [_normalize_stmt(s) for s in candidate]

    if len(orig_normalized) != len(cand_normalized):
        return False, f"statement count {len(orig_normalized)} vs {len(cand_normalized)}"

    for i, (o, c) in enumerate(zip(orig_normalized, cand_normalized)):
        if o != c:
            otype = original[i].get('type', '?')
            otext = (original[i].get('text') or '')[:50]
            ctype = candidate[i].get('type', '?')
            ctext = (candidate[i].get('text') or '')[:50]
            return False, f"statement {i} differs: {otype}:{otext} vs {ctype}:{ctext}"

    return True, "body matches"


def compare_specs(original_ast_path: Path, candidate_ast_path: Path) -> tuple[bool, str]:
    """Compare formal specs from two AST mappings (superset check).

    The candidate must contain ALL original functions/predicates and methods
    with identical requires/ensures/invariants. The candidate MAY add new
    helper lemmas, functions, or predicates — that's valid.

    Returns (match, message).
    """
    try:
        orig = json.loads(original_ast_path.read_text())
        cand = json.loads(candidate_ast_path.read_text())
    except (json.JSONDecodeError, FileNotFoundError) as e:
        return False, f"AST parse error: {e}"

    orig_spec = extract_spec_from_ast(orig)
    cand_spec = extract_spec_from_ast(cand)

    # All original functions must still exist (new ones are OK)
    orig_fns = set(orig_spec["functions"])
    cand_fns = set(cand_spec["functions"])
    missing_fns = orig_fns - cand_fns
    if missing_fns:
        return False, f"Missing functions: {sorted(missing_fns)}"

    # All original methods must exist with identical spec (new lemmas OK)
    orig_methods = {m["name"]: m for m in orig_spec["methods"]}
    cand_methods = {m["name"]: m for m in cand_spec["methods"]}

    for name, om in orig_methods.items():
        if name not in cand_methods:
            return False, f"Missing method: {name}"
        cm = cand_methods[name]
        if om["requires"] != cm["requires"]:
            return False, f"Method {name}: requires differ"
        if om["ensures"] != cm["ensures"]:
            return False, f"Method {name}: ensures differ"
        if om["invariants"] != cm["invariants"]:
            return False, f"Method {name}: invariants differ"
        # Body check: original statements must be a subtree of candidate
        orig_body = om.get("bodyStatements", [])
        cand_body = cm.get("bodyStatements", [])
        if orig_body:
            body_ok, body_msg = _body_matches(orig_body, cand_body)
            if not body_ok:
                return False, f"Method {name}: body changed — {body_msg}"

    added = set(cand_methods.keys()) - set(orig_methods.keys())
    added_fns = cand_fns - orig_fns
    extras = []
    if added:
        extras.append(f"added methods: {sorted(added)}")
    if added_fns:
        extras.append(f"added functions: {sorted(added_fns)}")
    msg = "Specs match" + (f" ({', '.join(extras)})" if extras else "")
    return True, msg


def run_dafny(code: str, tmp_dir: Path,
              original_ast_path: Path | None = None) -> tuple[bool, str, float, str]:
    """Write code to temp file, run dafny verify with AST mapping.

    Returns (success, output, time, spec_check_msg).
    If original_ast_path is provided, compares specs and rejects if different.
    """
    dfy_path = tmp_dir / "attempt.dfy"
    dfy_path.write_text(code)
    ast_path = tmp_dir / "attempt_ast.json"

    cmd = [DAFNY, str(DAFNY_DLL), "verify", str(dfy_path),
           "--verification-time-limit", str(VERIFY_TIMEOUT),
           "--ast-mapping", str(ast_path)]
    if Z3_PATH:
        cmd.extend(["--solver-path", Z3_PATH])

    t0 = time.perf_counter()
    try:
        result = subprocess.run(cmd, capture_output=True, text=True, timeout=VERIFY_TIMEOUT + 30)
        output = result.stdout + "\n" + result.stderr
    except subprocess.TimeoutExpired:
        output = "TIMEOUT: dafny verify exceeded time limit"
    except FileNotFoundError:
        output = f"ERROR: dafny not found at {DAFNY}"

    elapsed = time.perf_counter() - t0
    verified = "0 errors" in output

    # Spec comparison
    spec_msg = ""
    if original_ast_path and ast_path.exists():
        spec_ok, spec_msg = compare_specs(original_ast_path, ast_path)
        if not spec_ok:
            verified = False  # reject even if dafny says 0 errors
            output += f"\nSPEC_CHANGED: {spec_msg}"

    return verified, output.strip(), round(elapsed, 2), spec_msg


# ---------------------------------------------------------------------------
# Prompt building
# ---------------------------------------------------------------------------

def build_prompt(stripped_code: str, dafny_error: str | None = None,
                 attempt: int = 1) -> str:
    """Build prompt for the LLM."""
    if attempt == 1 or dafny_error is None:
        return f"""The following Dafny program has a correct implementation and specification, but verification fails because some `assert` statements are missing. The program verified successfully before these assertions were removed.

RULES — read carefully:
1. Add `assert` statements to make `dafny verify` pass.
2. You may add helper lemmas or ghost functions if needed.
3. You MUST NOT modify ANY existing code. Do not change variable names, assignments, control flow, loop bodies, if/else branches, return statements, or any expression.
4. You MUST NOT modify ANY formal specification. Do not change requires, ensures, invariant, decreases, function bodies, or predicate bodies.
5. Any modification to existing code or specifications will be automatically detected and rejected. We compare the AST of your output against the original — only added assert statements and new lemma/function definitions are permitted.

Return the complete Dafny program with your added assertions inside <DAFNY_CODE> tags.

```dafny
{stripped_code}
```

<DAFNY_CODE>
"""
    else:
        return f"""Your previous attempt failed verification. Here is the error:

{dafny_error}

REMINDER: Do NOT modify any existing code or specifications. Only add `assert` statements (and optionally helper lemmas). Any code modification will be automatically detected and rejected.

The original program (without assertions) is:

```dafny
{stripped_code}
```

Fix the assertions and return the complete program inside <DAFNY_CODE> tags.

<DAFNY_CODE>
"""


# ---------------------------------------------------------------------------
# Single problem benchmark
# ---------------------------------------------------------------------------

def run_problem(problem_name: str, inputs_dir: Path, output_dir: Path,
                backend: str, url: str, temperature: float = 0.7) -> dict:
    """Run benchmark on a single problem. Returns result dict."""
    problem_input = inputs_dir / problem_name
    meta = json.loads((problem_input / "meta.json").read_text())
    stripped_code = (problem_input / "stripped.dfy").read_text()

    # Reference AST for spec comparison
    ref_ast_path = problem_input / "reference_ast.json"
    if not ref_ast_path.exists():
        ref_ast_path = None

    # Setup output
    problem_out = output_dir / problem_name
    problem_out.mkdir(parents=True, exist_ok=True)
    tmp_dir = problem_out / "tmp"
    tmp_dir.mkdir(exist_ok=True)

    call_fn = call_sglang if backend == "sglang" else call_llama

    result = {
        "problem": problem_name,
        "essential_count": meta["essential_count"],
        "backend": backend,
        "model": "gpt-oss-20b",
        "temperature": temperature,
        "start_time": datetime.now().isoformat(),
        "attempts": [],
        "success": False,
        "total_time": 0,
        "total_tokens": 0,
        "total_prompt_tokens": 0,
    }

    t_start = time.perf_counter()
    dafny_error = None
    attempt = 0

    while True:
        elapsed_total = time.perf_counter() - t_start
        if elapsed_total >= TIMEOUT_PER_PROBLEM:
            break

        attempt += 1
        attempt_data = {"attempt": attempt, "start_time": datetime.now().isoformat()}

        # Build prompt
        prompt = build_prompt(stripped_code, dafny_error, attempt)
        attempt_data["prompt"] = prompt
        attempt_data["prompt_length"] = len(prompt)

        # Call LLM
        print(f"  [{problem_name}] Attempt {attempt}...")
        llm_result = call_fn(url, prompt, temperature=temperature)

        attempt_data["llm_response"] = llm_result["text"]
        attempt_data["llm_tokens"] = llm_result.get("tokens", 0)
        attempt_data["llm_prompt_tokens"] = llm_result.get("prompt_tokens", 0)
        attempt_data["llm_time"] = llm_result.get("time", 0)
        attempt_data["llm_error"] = llm_result.get("error", None)

        result["total_tokens"] += llm_result.get("tokens", 0)
        result["total_prompt_tokens"] += llm_result.get("prompt_tokens", 0)

        if llm_result.get("error"):
            err_msg = llm_result["error"][:200]
            print(f"  [{problem_name}] LLM error: {err_msg}")
            attempt_data["dafny_success"] = False
            attempt_data["dafny_output"] = ""
            attempt_data["llm_error"] = llm_result["error"]
            result["attempts"].append(attempt_data)
            # Don't retry on fatal errors
            if "out of memory" in llm_result["error"].lower():
                break
            # Sleep before retry to avoid spin loop
            time.sleep(5)
            continue

        # Extract code
        code = extract_code(llm_result["text"])
        attempt_data["extracted_code"] = code

        if not code or "method" not in code:
            print(f"  [{problem_name}] Could not extract code")
            attempt_data["dafny_success"] = False
            attempt_data["dafny_output"] = "CODE_EXTRACTION_FAILED"
            result["attempts"].append(attempt_data)
            dafny_error = "Could not extract valid Dafny code from your response. Please return the complete program inside <DAFNY_CODE> tags."
            continue

        # Run dafny verify
        success, dafny_output, verify_time, spec_msg = run_dafny(code, tmp_dir, ref_ast_path)
        attempt_data["dafny_success"] = success
        attempt_data["dafny_output"] = dafny_output
        attempt_data["dafny_time"] = verify_time
        attempt_data["spec_check"] = spec_msg

        result["attempts"].append(attempt_data)

        if success:
            print(f"  [{problem_name}] VERIFIED on attempt {attempt}!")
            result["success"] = True
            result["verified_code"] = code
            break
        else:
            # Extract error for retry prompt
            error_lines = [l for l in dafny_output.split("\n")
                          if "Error" in l or "error" in l or "could not be proved" in l]
            dafny_error = "\n".join(error_lines[:10]) if error_lines else dafny_output[:500]
            print(f"  [{problem_name}] Attempt {attempt} failed ({verify_time}s)")

    result["total_time"] = round(time.perf_counter() - t_start, 2)
    result["total_attempts"] = attempt
    result["end_time"] = datetime.now().isoformat()

    # Write result
    (problem_out / "result.json").write_text(json.dumps(result, indent=2, default=str))

    # Write log (human-readable)
    with open(problem_out / "log.txt", "w") as f:
        f.write(f"Problem: {problem_name}\n")
        f.write(f"Essential assertions: {meta['essential_count']}\n")
        f.write(f"Result: {'SUCCESS' if result['success'] else 'FAILED'}\n")
        f.write(f"Attempts: {result['total_attempts']}\n")
        f.write(f"Total time: {result['total_time']}s\n")
        f.write(f"Total tokens: {result['total_tokens']}\n\n")
        for a in result["attempts"]:
            f.write(f"{'='*60}\n")
            f.write(f"ATTEMPT {a['attempt']}\n")
            f.write(f"{'='*60}\n")
            f.write(f"\n--- PROMPT ({a['prompt_length']} chars) ---\n")
            f.write(a["prompt"][:2000] + ("..." if len(a["prompt"]) > 2000 else "") + "\n")
            f.write(f"\n--- LLM RESPONSE ({a['llm_tokens']} tokens, {a['llm_time']}s) ---\n")
            f.write(a["llm_response"][:5000] + "\n")
            f.write(f"\n--- DAFNY OUTPUT ---\n")
            f.write(a["dafny_output"][:2000] + "\n")
            f.write(f"\n--- RESULT: {'PASS' if a.get('dafny_success') else 'FAIL'} ---\n\n")

    status = "PASS" if result["success"] else "FAIL"
    print(f"  [{problem_name}] {status} ({result['total_attempts']} attempts, {result['total_time']}s, {result['total_tokens']} tokens)")
    return result


# ---------------------------------------------------------------------------
# Main
# ---------------------------------------------------------------------------

def main():
    parser = argparse.ArgumentParser(description="LLM Dafny assertion benchmark")
    parser.add_argument("--inputs-dir", type=str, required=True, help="Directory with prepared inputs")
    parser.add_argument("--output-dir", type=str, default="benchmark_results", help="Output directory")
    parser.add_argument("--backend", choices=["sglang", "llama"], default="sglang")
    parser.add_argument("--url", type=str, default="http://127.0.0.1:8000")
    parser.add_argument("--names", nargs="+", help="Specific problem names")
    parser.add_argument("--workers", type=int, default=1, help="Parallel problems (use >1 with SGLang)")
    parser.add_argument("--temperature", type=float, default=0.7)
    parser.add_argument("--timeout", type=int, default=500, help="Seconds per problem")
    args = parser.parse_args()

    global TIMEOUT_PER_PROBLEM
    TIMEOUT_PER_PROBLEM = args.timeout

    inputs_dir = Path(args.inputs_dir)
    output_dir = Path(args.output_dir)
    output_dir.mkdir(parents=True, exist_ok=True)

    manifest = json.loads((inputs_dir / "manifest.json").read_text())

    if args.names:
        names = args.names
    else:
        names = manifest["problems"]

    print(f"Benchmark: {len(names)} problems, backend={args.backend}, workers={args.workers}")
    print(f"Timeout: {args.timeout}s per problem, URL: {args.url}")
    print()

    t0 = time.perf_counter()
    all_results = []

    if args.workers == 1:
        for name in names:
            r = run_problem(name, inputs_dir, output_dir, args.backend, args.url, args.temperature)
            all_results.append(r)
    else:
        from concurrent.futures import ThreadPoolExecutor, as_completed
        with ThreadPoolExecutor(max_workers=args.workers) as executor:
            futures = {
                executor.submit(run_problem, name, inputs_dir, output_dir,
                               args.backend, args.url, args.temperature): name
                for name in names
            }
            for future in as_completed(futures):
                name = futures[future]
                try:
                    r = future.result()
                    all_results.append(r)
                except Exception as e:
                    print(f"  [{name}] ERROR: {e}")
                    all_results.append({"problem": name, "error": str(e)})

    total_time = round(time.perf_counter() - t0, 1)
    successes = sum(1 for r in all_results if r.get("success"))

    # Write summary
    summary = {
        "timestamp": datetime.now().isoformat(),
        "backend": args.backend,
        "model": "gpt-oss-20b",
        "total_problems": len(all_results),
        "successes": successes,
        "failures": len(all_results) - successes,
        "success_rate": round(successes / len(all_results) * 100, 1) if all_results else 0,
        "total_time": total_time,
        "total_tokens": sum(r.get("total_tokens", 0) for r in all_results),
        "per_problem": [
            {
                "problem": r["problem"],
                "success": r.get("success", False),
                "attempts": r.get("total_attempts", 0),
                "time": r.get("total_time", 0),
                "tokens": r.get("total_tokens", 0),
                "essential_count": r.get("essential_count", 0),
            }
            for r in all_results
        ],
    }
    (output_dir / "summary.json").write_text(json.dumps(summary, indent=2))

    print(f"\n{'='*60}")
    print(f"BENCHMARK COMPLETE")
    print(f"{'='*60}")
    print(f"Problems: {len(all_results)}")
    print(f"Success:  {successes}/{len(all_results)} ({summary['success_rate']}%)")
    print(f"Time:     {total_time}s")
    print(f"Tokens:   {summary['total_tokens']}")
    print(f"Results:  {output_dir}/summary.json")


if __name__ == "__main__":
    main()

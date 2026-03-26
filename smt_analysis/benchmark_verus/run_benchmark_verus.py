#!/usr/bin/env python3
from __future__ import annotations
"""
LLM benchmark for Verus: can the model recover stripped essential assertions?

For each problem, the LLM receives verified Verus code with all essential
assertions removed and must add assertions to make verus pass again.

Adapted from run_benchmark.py (Dafny version). The LLM backend code is
identical; only the verification command, prompt, and code extraction differ.

Usage:
    python3 run_benchmark_verus.py --inputs-dir ./inputs --backend sglang --url http://127.0.0.1:8000
    python3 run_benchmark_verus.py --inputs-dir ./inputs --backend llama --url http://127.0.0.1:8080
    python3 run_benchmark_verus.py --inputs-dir ./inputs --names 0025_1096_A --workers 1
"""

import argparse
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

VERUS_BIN = os.environ.get("VERUS_BIN", "/tmp/verus_install/verus-arm64-macos/verus")
SINGULARITY_SIF = os.environ.get("VERUS_SIF", "")  # set on Leonardo
TIMEOUT_PER_PROBLEM = 500
MAX_TOKENS = 8192
VERIFY_TIMEOUT = 60

SYSTEM_MSG = "You are a Verus verification expert. Output only code, no explanations."

# Model config from env
_CHAT_API = os.environ.get("BENCHMARK_CHAT_API", "false").lower() == "true"
_CHAT_TEMPLATE = os.environ.get("BENCHMARK_CHAT_TEMPLATE", (
    "<|start|>system<|message|>{system}<|end|>"
    "<|start|>user<|message|>{user}<|end|>"
    "<|start|>assistant<|channel|>final<|message|>"
))
_EXTRA_STOP = os.environ.get("BENCHMARK_STOP_TOKENS", "").split("|")
_EXTRA_STOP = [s for s in _EXTRA_STOP if s]


# ---------------------------------------------------------------------------
# LLM backends (identical to Dafny version)
# ---------------------------------------------------------------------------

def call_sglang(url: str, prompt: str, max_tokens: int = MAX_TOKENS,
                temperature: float = 0.7) -> dict:
    import urllib.request

    if _CHAT_API:
        payload = json.dumps({
            "model": "default",
            "messages": [
                {"role": "system", "content": SYSTEM_MSG},
                {"role": "user", "content": prompt},
            ],
            "max_tokens": max_tokens,
            "temperature": temperature,
            "stop": ["</VERUS_CODE>"] + _EXTRA_STOP,
        }).encode("utf-8")
        api_url = f"{url}/v1/chat/completions"
    else:
        formatted = _CHAT_TEMPLATE.format(system=SYSTEM_MSG, user=prompt)
        payload = json.dumps({
            "text": formatted,
            "sampling_params": {
                "max_new_tokens": max_tokens,
                "temperature": temperature,
                "stop": ["</VERUS_CODE>"] + _EXTRA_STOP,
            },
        }).encode("utf-8")
        api_url = f"{url}/generate"

    req = urllib.request.Request(api_url, data=payload,
                                 headers={"Content-Type": "application/json"})

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
    reasoning = ""

    if _CHAT_API:
        choices = result.get("choices", [])
        msg = choices[0].get("message", {}) if choices else {}
        text = msg.get("content", "")
        reasoning = msg.get("reasoning_content", "")
        usage = result.get("usage", {})
        tokens = usage.get("completion_tokens", 0)
        prompt_tokens = usage.get("prompt_tokens", 0)
    else:
        raw_text = result.get("text", "")
        analysis_match = re.search(r'<\|channel\|>analysis<\|message\|>(.*?)(?:<\|channel\|>|<\|end\|>|$)',
                                    raw_text, re.DOTALL)
        if analysis_match:
            reasoning = analysis_match.group(1).strip()
        final_match = re.search(r'<\|channel\|>final<\|message\|>(.*?)(?:<\|end\|>|$)',
                                 raw_text, re.DOTALL)
        text = final_match.group(1).strip() if final_match else raw_text
        meta = result.get("meta_info", {})
        tokens = meta.get("completion_tokens", 0)
        prompt_tokens = meta.get("prompt_tokens", 0)

    return {
        "text": text, "reasoning": reasoning,
        "tokens": tokens, "prompt_tokens": prompt_tokens,
        "time": round(elapsed, 2), "raw": result,
    }


def call_llama(url: str, prompt: str, max_tokens: int = MAX_TOKENS,
               temperature: float = 0.7) -> dict:
    import urllib.request

    payload = json.dumps({
        "model": "default",
        "messages": [
            {"role": "system", "content": SYSTEM_MSG},
            {"role": "user", "content": prompt},
        ],
        "max_tokens": max_tokens,
        "temperature": temperature,
        "stop": ["</VERUS_CODE>"],
    }).encode("utf-8")

    req = urllib.request.Request(
        f"{url}/v1/chat/completions", data=payload,
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
    msg = choices[0].get("message", {}) if choices else {}
    usage = result.get("usage", {})

    return {
        "text": msg.get("content", ""),
        "reasoning": msg.get("reasoning_content", ""),
        "tokens": usage.get("completion_tokens", 0),
        "prompt_tokens": usage.get("prompt_tokens", 0),
        "time": round(elapsed, 2), "raw": result,
    }


# ---------------------------------------------------------------------------
# Code extraction
# ---------------------------------------------------------------------------

def extract_code(response: str) -> str | None:
    """Extract Verus code from LLM response."""
    for pattern in [
        r'<VERUS_CODE>\s*(.*?)(?:</VERUS_CODE>|$)',
        r'<code>\s*(.*?)(?:</code>|$)',
    ]:
        m = re.search(pattern, response, re.DOTALL | re.IGNORECASE)
        if m:
            return m.group(1).strip()

    for pattern in [r'```rust\s*(.*?)\s*```', r'```\s*(.*?)\s*```']:
        m = re.search(pattern, response, re.DOTALL)
        if m:
            return m.group(1).strip()

    # Find from verus! macro
    m = re.search(r'(use vstd::prelude::\*;.*)', response, re.DOTALL)
    if m:
        return m.group(1).strip()

    return None


# ---------------------------------------------------------------------------
# Verus verification + integrity check
# ---------------------------------------------------------------------------

def run_verus(code: str, tmp_dir: Path,
              original_path: Path | None = None) -> tuple[bool, str, float, str]:
    """Write code to temp file, run verus.

    Returns (success, output, time, integrity_msg).
    If original_path is provided, runs skeleton integrity check.
    """
    rs_path = tmp_dir / "attempt.rs"
    rs_path.write_text(code)

    # Build verus command
    if SINGULARITY_SIF:
        cmd = [
            "singularity", "exec",
            "--bind", "/leonardo_work:/leonardo_work",
            "--bind", "/leonardo/home:/leonardo/home",
            "--env", f"PATH={os.environ.get('CARGO_BIN', '/usr/bin')}:$PATH",
            "--env", f"RUSTUP_HOME={os.environ.get('RUSTUP_HOME', '')}",
            "--env", f"CARGO_HOME={os.environ.get('CARGO_HOME', '')}",
            SINGULARITY_SIF,
            VERUS_BIN, str(rs_path),
            "--rlimit", str(VERIFY_TIMEOUT),
        ]
    else:
        cmd = [VERUS_BIN, str(rs_path), "--rlimit", str(VERIFY_TIMEOUT)]

    t0 = time.perf_counter()
    try:
        result = subprocess.run(cmd, capture_output=True, text=True,
                               timeout=VERIFY_TIMEOUT + 60)
        output = result.stdout + "\n" + result.stderr
    except subprocess.TimeoutExpired:
        output = "TIMEOUT: verus exceeded time limit"
    except FileNotFoundError:
        output = f"ERROR: verus not found at {VERUS_BIN}"

    elapsed = time.perf_counter() - t0
    verified = "0 errors" in output and result.returncode == 0

    # Integrity check
    integrity_msg = ""
    if original_path and verified:
        try:
            sys.path.insert(0, str(Path(__file__).parent.parent / "verus_translation"))
            from verus_integrity_check import check_integrity
            ok, integrity_msg = check_integrity(original_path, rs_path)
            if not ok:
                verified = False
                output += f"\nINTEGRITY_FAILED: {integrity_msg}"
        except Exception as e:
            integrity_msg = f"integrity check error: {e}"

    return verified, output.strip(), round(elapsed, 2), integrity_msg


# ---------------------------------------------------------------------------
# Prompt building
# ---------------------------------------------------------------------------

def build_prompt(stripped_code: str, verus_error: str | None = None,
                 attempt: int = 1) -> str:
    if attempt == 1 or verus_error is None:
        return f"""The following Verus program has a correct implementation and specification, but verification fails because some `assert` statements and `proof` blocks are missing. The program verified successfully before these were removed.

RULES — read carefully:
1. Add `assert(...)` statements and `proof {{ }}` blocks to make `verus` verification pass.
2. You may add `proof fn` helper lemmas if needed.
3. You MUST NOT modify ANY existing code. Do not change variable names, assignments, control flow, loop bodies, if/else branches, return statements, or any expression.
4. You MUST NOT modify ANY formal specification. Do not change `requires`, `ensures`, `invariant`, `decreases`, `spec fn` bodies, or function signatures.
5. Any modification to existing code or specifications will be automatically detected and rejected.

Verus hints:
- Use `assert(expr)` for simple assertions
- Use `assert(expr) by {{ ... }}` for assertions needing proof steps
- Use `assert(expr) by(nonlinear_arith) requires ...;` for nonlinear arithmetic
- Use `assert forall|i: int| ... implies ... by {{ ... }};` for quantified assertions
- Use `proof {{ lemma_call(args); }}` to invoke helper lemmas in exec functions
- Use `=~=` for extensional sequence equality

Return the complete Verus program with your additions inside <VERUS_CODE> tags.

```rust
{stripped_code}
```

<VERUS_CODE>
"""
    else:
        return f"""Your previous attempt failed verification. Here is the error:

{verus_error}

REMINDER: Do NOT modify any existing code or specifications. Only add `assert` statements, `proof` blocks, and optionally helper `proof fn` lemmas. Any code modification will be automatically detected and rejected.

The original program (without assertions) is:

```rust
{stripped_code}
```

Fix the assertions and return the complete program inside <VERUS_CODE> tags.

<VERUS_CODE>
"""


# ---------------------------------------------------------------------------
# Single problem benchmark
# ---------------------------------------------------------------------------

def run_problem(problem_name: str, inputs_dir: Path, output_dir: Path,
                backend: str, url: str, temperature: float = 0.7) -> dict:
    problem_input = inputs_dir / problem_name
    meta = json.loads((problem_input / "meta.json").read_text())
    stripped_code = (problem_input / "stripped.rs").read_text()

    # Original file for integrity check
    original_path = None
    verus_dir = Path(__file__).parent.parent / "verus_translation" / "programs" / problem_name
    for candidate in ["verified_not_brittle.rs", "verified.rs"]:
        p = verus_dir / candidate
        if p.exists():
            original_path = p
            break

    problem_out = output_dir / problem_name
    problem_out.mkdir(parents=True, exist_ok=True)
    tmp_dir = problem_out / "tmp"
    tmp_dir.mkdir(exist_ok=True)

    call_fn = call_sglang if backend == "sglang" else call_llama

    result = {
        "problem": problem_name,
        "essential_count": meta["essential_count"],
        "backend": backend,
        "model": os.environ.get("BENCHMARK_MODEL", "unknown"),
        "temperature": temperature,
        "start_time": datetime.now().isoformat(),
        "attempts": [],
        "success": False,
        "total_time": 0,
        "total_tokens": 0,
        "total_prompt_tokens": 0,
    }

    t_start = time.perf_counter()
    verus_error = None
    attempt = 0

    while True:
        elapsed_total = time.perf_counter() - t_start
        if elapsed_total >= TIMEOUT_PER_PROBLEM:
            break

        attempt += 1
        attempt_data = {"attempt": attempt, "start_time": datetime.now().isoformat()}

        prompt = build_prompt(stripped_code, verus_error, attempt)
        attempt_data["prompt"] = prompt
        attempt_data["prompt_length"] = len(prompt)

        print(f"  [{problem_name}] Attempt {attempt}...")
        llm_result = call_fn(url, prompt, temperature=temperature)

        attempt_data["llm_response"] = llm_result["text"]
        attempt_data["llm_reasoning"] = llm_result.get("reasoning", "")
        attempt_data["llm_tokens"] = llm_result.get("tokens", 0)
        attempt_data["llm_prompt_tokens"] = llm_result.get("prompt_tokens", 0)
        attempt_data["llm_time"] = llm_result.get("time", 0)
        attempt_data["llm_error"] = llm_result.get("error", None)

        result["total_tokens"] += llm_result.get("tokens", 0)
        result["total_prompt_tokens"] += llm_result.get("prompt_tokens", 0)

        if llm_result.get("error"):
            err_msg = llm_result["error"][:200]
            print(f"  [{problem_name}] LLM error: {err_msg}")
            attempt_data["verus_success"] = False
            attempt_data["verus_output"] = ""
            result["attempts"].append(attempt_data)
            if "out of memory" in llm_result["error"].lower():
                break
            time.sleep(5)
            continue

        code = extract_code(llm_result["text"])
        attempt_data["extracted_code"] = code

        if not code or "verus!" not in code:
            print(f"  [{problem_name}] Could not extract code")
            attempt_data["verus_success"] = False
            attempt_data["verus_output"] = "CODE_EXTRACTION_FAILED"
            result["attempts"].append(attempt_data)
            verus_error = "Could not extract valid Verus code from your response. Please return the complete program inside <VERUS_CODE> tags."
            continue

        success, verus_output, verify_time, integrity_msg = run_verus(
            code, tmp_dir, original_path)
        attempt_data["verus_success"] = success
        attempt_data["verus_output"] = verus_output
        attempt_data["verus_time"] = verify_time
        attempt_data["integrity_check"] = integrity_msg

        result["attempts"].append(attempt_data)

        if success:
            print(f"  [{problem_name}] VERIFIED on attempt {attempt}!")
            result["success"] = True
            result["verified_code"] = code
            break
        else:
            error_lines = [l for l in verus_output.split("\n")
                          if "error" in l.lower() or "assertion failed" in l.lower()
                          or "INTEGRITY_FAILED" in l]
            verus_error = "\n".join(error_lines[:10]) if error_lines else verus_output[:500]
            print(f"  [{problem_name}] Attempt {attempt} failed ({verify_time}s)")

    result["total_time"] = round(time.perf_counter() - t_start, 2)
    result["total_attempts"] = attempt
    result["end_time"] = datetime.now().isoformat()

    (problem_out / "result.json").write_text(json.dumps(result, indent=2, default=str))

    with open(problem_out / "log.txt", "w") as f:
        f.write(f"Problem: {problem_name}\n")
        f.write(f"Essential assertions: {meta['essential_count']}\n")
        f.write(f"Result: {'SUCCESS' if result['success'] else 'FAILED'}\n")
        f.write(f"Attempts: {result['total_attempts']}\n")
        f.write(f"Total time: {result['total_time']}s\n")
        f.write(f"Total tokens: {result['total_tokens']}\n\n")
        for a in result["attempts"]:
            f.write(f"{'='*60}\n")
            f.write(f"ATTEMPT {a['attempt']}\n{'='*60}\n")
            f.write(f"\n--- LLM RESPONSE ({a.get('llm_tokens',0)} tokens, {a.get('llm_time',0)}s) ---\n")
            f.write((a.get("llm_response") or "")[:5000] + "\n")
            f.write(f"\n--- VERUS OUTPUT ---\n")
            f.write((a.get("verus_output") or "")[:2000] + "\n")
            f.write(f"\n--- RESULT: {'PASS' if a.get('verus_success') else 'FAIL'} ---\n\n")

    status = "PASS" if result["success"] else "FAIL"
    print(f"  [{problem_name}] {status} ({result['total_attempts']} attempts, {result['total_time']}s, {result['total_tokens']} tokens)")
    return result


# ---------------------------------------------------------------------------
# Main
# ---------------------------------------------------------------------------

def main():
    parser = argparse.ArgumentParser(description="LLM Verus assertion benchmark")
    parser.add_argument("--inputs-dir", type=str, required=True)
    parser.add_argument("--output-dir", type=str, default="benchmark_results")
    parser.add_argument("--backend", choices=["sglang", "llama"], default="sglang")
    parser.add_argument("--url", type=str, default="http://127.0.0.1:8000")
    parser.add_argument("--names", nargs="+")
    parser.add_argument("--workers", type=int, default=1)
    parser.add_argument("--temperature", type=float, default=0.7)
    parser.add_argument("--timeout", type=int, default=500)
    args = parser.parse_args()

    global TIMEOUT_PER_PROBLEM
    TIMEOUT_PER_PROBLEM = args.timeout

    inputs_dir = Path(args.inputs_dir)
    output_dir = Path(args.output_dir)
    output_dir.mkdir(parents=True, exist_ok=True)

    manifest = json.loads((inputs_dir / "manifest.json").read_text())
    names = args.names if args.names else manifest["problems"]

    print(f"Verus Benchmark: {len(names)} problems, backend={args.backend}, workers={args.workers}")
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
                    all_results.append(future.result())
                except Exception as e:
                    print(f"  [{name}] ERROR: {e}")
                    all_results.append({"problem": name, "error": str(e)})

    total_time = round(time.perf_counter() - t0, 1)
    successes = sum(1 for r in all_results if r.get("success"))

    summary = {
        "timestamp": datetime.now().isoformat(),
        "backend": args.backend,
        "model": os.environ.get("BENCHMARK_MODEL", "unknown"),
        "total_problems": len(all_results),
        "successes": successes,
        "failures": len(all_results) - successes,
        "success_rate": round(successes / len(all_results) * 100, 1) if all_results else 0,
        "total_time": total_time,
        "total_tokens": sum(r.get("total_tokens", 0) for r in all_results),
        "per_problem": [
            {"problem": r["problem"], "success": r.get("success", False),
             "attempts": r.get("total_attempts", 0), "time": r.get("total_time", 0),
             "tokens": r.get("total_tokens", 0), "essential_count": r.get("essential_count", 0)}
            for r in all_results
        ],
    }
    (output_dir / "summary.json").write_text(json.dumps(summary, indent=2))

    print(f"\n{'='*60}")
    print(f"VERUS BENCHMARK COMPLETE")
    print(f"{'='*60}")
    print(f"Problems: {len(all_results)}")
    print(f"Success:  {successes}/{len(all_results)} ({summary['success_rate']}%)")
    print(f"Time:     {total_time}s")
    print(f"Tokens:   {summary['total_tokens']}")
    print(f"Results:  {output_dir}/summary.json")


if __name__ == "__main__":
    main()

#!/usr/bin/env python3
from __future__ import annotations
"""
Placeholder benchmark: LLM fills in assertion placeholders.

Unlike run_benchmark.py (where the LLM rewrites the whole program),
here we:
1. Replace each essential assertion with a numbered placeholder
2. Ask the LLM to output ONLY the assertions (one per placeholder)
3. Insert them back programmatically and run dafny verify

This eliminates code modification risk and measures per-assertion accuracy.

Usage:
    python3 run_placeholder.py --inputs-dir ./inputs --backend sglang --url http://127.0.0.1:8000
    python3 run_placeholder.py --inputs-dir ./inputs --backend llama --url http://127.0.0.1:8080
    python3 run_placeholder.py --inputs-dir ./inputs --names 0000_1013_A --workers 1
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

DAFNY = os.environ.get("DOTNET8", os.environ.get("DOTNET", "dotnet"))
DAFNY_DLL = os.environ.get("DAFNY_DLL", "Dafny.dll")
Z3_PATH = os.environ.get("Z3_PATH", None)
TIMEOUT_PER_PROBLEM = 500
MAX_TOKENS = 4096
VERIFY_TIMEOUT = 60

SYSTEM_MSG = "You are a Dafny verification expert. Output only the requested JSON, no explanations."


def _find_assert_end(lines: list, start: int) -> int:
    """Find end line (inclusive) of an assert statement starting at `start`."""
    j = start
    while j < len(lines):
        stripped = lines[j].strip()
        if "by {" in stripped or "by{" in stripped:
            depth = stripped.count("{") - stripped.count("}")
            j += 1
            while j < len(lines) and depth > 0:
                depth += lines[j].count("{") - lines[j].count("}")
                j += 1
            return j - 1
        if stripped.endswith(";"):
            k = j + 1
            while k < len(lines) and lines[k].strip() == "":
                k += 1
            if k < len(lines) and lines[k].strip().startswith("by"):
                j = k
                continue
            return j
        j += 1
    return min(j, len(lines) - 1)

GPT_OSS_TEMPLATE = (
    "<|start|>system<|message|>{system}<|end|>"
    "<|start|>user<|message|>{user}<|end|>"
    "<|start|>assistant<|channel|>final<|message|>"
)


# ---------------------------------------------------------------------------
# Placeholder generation
# ---------------------------------------------------------------------------

def make_placeholder_code(source_path: Path, assertions: list[dict]) -> tuple[str, list[dict]]:
    """Replace essential assertions with numbered placeholders.

    Returns (placeholder_code, placeholder_info) where placeholder_info
    is a list of {id, line, original_text, indent} ordered by line number.
    """
    lines = source_path.read_text().split("\n")

    # Sort by line ascending, assign IDs in file order
    essentials = sorted(assertions, key=lambda a: a["line"])

    # First pass: collect placeholder info with temp markers
    placeholders = []
    for pid, a in enumerate(essentials):
        start = a["line"] - 1
        if start < 0 or start >= len(lines):
            continue
        indent = len(lines[start]) - len(lines[start].lstrip())
        placeholders.append({
            "id": pid,
            "line": a["line"],
            "line_idx": start,
            "original_text": a.get("text", ""),
            "indent": indent,
        })

    # Second pass: replace lines in reverse order (so line numbers don't shift)
    for p in reversed(placeholders):
        start = p["line_idx"]
        indent_str = " " * p["indent"]
        pid = p["id"]

        stripped = lines[start].strip()
        if stripped.startswith("assert "):
            end = _find_assert_end(lines, start)
            for j in range(start, end + 1):
                lines[j] = ""
            lines[start] = f"{indent_str}// PLACEHOLDER_{pid}: insert assertion here"
        else:
            text = p["original_text"]
            for pattern in [text, f" {text}"]:
                if pattern in lines[start]:
                    lines[start] = lines[start].replace(
                        pattern, f" /* PLACEHOLDER_{pid} */", 1)
                    break

    # Clean up line_idx from output
    for p in placeholders:
        del p["line_idx"]

    return "\n".join(lines), placeholders


# ---------------------------------------------------------------------------
# Prompt
# ---------------------------------------------------------------------------

def build_prompt(placeholder_code: str, placeholders: list[dict],
                 dafny_error: str | None = None, attempt: int = 1) -> str:
    """Build prompt asking LLM to fill in placeholders."""
    placeholder_list = "\n".join(
        f"  PLACEHOLDER_{p['id']}: (line {p['line']})" for p in placeholders
    )

    if attempt == 1 or dafny_error is None:
        return f"""The following Dafny program has numbered placeholders where `assert` statements are needed to make verification pass.

For each placeholder, provide the assertion that should go there. Output a JSON array with one entry per placeholder:

```json
[
  {{"id": 0, "assertion": "assert x[..i + 1] == x[..i] + [x[i]];"}},
  {{"id": 1, "assertion": "assert x[..|x|] == x;"}}
]
```

RULES:
- Each assertion must be a valid Dafny `assert` statement ending with `;`
- Do not include any other code — only assertions
- Output ONLY the JSON array, nothing else

Placeholders:
{placeholder_list}

```dafny
{placeholder_code}
```"""
    else:
        return f"""Your previous assertions failed verification:

{dafny_error}

Provide corrected assertions for all placeholders. Output ONLY a JSON array:

```json
[{{"id": 0, "assertion": "assert ...;"}}, ...]
```

Placeholders:
{placeholder_list}

```dafny
{placeholder_code}
```"""


# ---------------------------------------------------------------------------
# Parse LLM response
# ---------------------------------------------------------------------------

def parse_assertions(response: str, n_placeholders: int) -> list[str] | None:
    """Parse JSON array of assertions from LLM response.

    Returns list of assertion strings (indexed by placeholder id), or None.
    """
    # Try to find JSON array in response
    # Strategy 1: find ```json ... ```
    m = re.search(r'```json\s*(\[.*?\])\s*```', response, re.DOTALL)
    if m:
        text = m.group(1)
    else:
        # Strategy 2: find [ ... ]
        m = re.search(r'\[.*\]', response, re.DOTALL)
        if m:
            text = m.group(0)
        else:
            return None

    try:
        items = json.loads(text)
    except json.JSONDecodeError:
        # Try fixing common issues: trailing commas, single quotes
        text = re.sub(r',\s*\]', ']', text)
        text = text.replace("'", '"')
        try:
            items = json.loads(text)
        except json.JSONDecodeError:
            return None

    if not isinstance(items, list):
        return None

    # Build assertion list indexed by id
    result = [""] * n_placeholders
    for item in items:
        if isinstance(item, dict):
            pid = item.get("id", -1)
            assertion = item.get("assertion", "")
            if 0 <= pid < n_placeholders and assertion:
                result[pid] = assertion
        elif isinstance(item, str):
            # Some models output just strings
            idx = len([r for r in result if r])
            if idx < n_placeholders:
                result[idx] = item

    return result if any(result) else None


# ---------------------------------------------------------------------------
# Insert assertions and verify
# ---------------------------------------------------------------------------

def fill_placeholders(placeholder_code: str, assertions: list[str],
                      placeholders: list[dict]) -> str:
    """Replace placeholders with actual assertions."""
    code = placeholder_code
    for p, assertion in zip(placeholders, assertions):
        pid = p["id"]
        indent_str = " " * p["indent"]
        # Ensure assertion ends with ;
        assertion = assertion.strip()
        if assertion and not assertion.endswith(";"):
            assertion += ";"

        # Replace placeholder comment with assertion
        code = code.replace(
            f"{indent_str}// PLACEHOLDER_{pid}: insert assertion here",
            f"{indent_str}{assertion}" if assertion else f"{indent_str}// PLACEHOLDER_{pid}: no assertion provided"
        )
        # Also handle inline placeholders
        code = code.replace(
            f"/* PLACEHOLDER_{pid} */",
            assertion if assertion else f"/* PLACEHOLDER_{pid}: no assertion */"
        )

    return code


def run_dafny(code: str, tmp_dir: Path) -> tuple[bool, str, float]:
    """Run dafny verify. Returns (success, output, time)."""
    dfy_path = tmp_dir / "attempt.dfy"
    dfy_path.write_text(code)

    cmd = [DAFNY, str(DAFNY_DLL), "verify", str(dfy_path),
           "--verification-time-limit", str(VERIFY_TIMEOUT)]
    if Z3_PATH:
        cmd.extend(["--solver-path", Z3_PATH])

    t0 = time.perf_counter()
    try:
        result = subprocess.run(cmd, capture_output=True, text=True, timeout=VERIFY_TIMEOUT + 30)
        output = result.stdout + "\n" + result.stderr
    except subprocess.TimeoutExpired:
        output = "TIMEOUT"
    except FileNotFoundError:
        output = f"ERROR: dafny not found at {DAFNY}"

    elapsed = time.perf_counter() - t0
    success = "0 errors" in output
    return success, output.strip(), round(elapsed, 2)


# ---------------------------------------------------------------------------
# LLM call
# ---------------------------------------------------------------------------

def call_llm(url: str, prompt: str, backend: str,
             max_tokens: int = MAX_TOKENS, temperature: float = 0.7) -> dict:
    """Call LLM (SGLang or llama.cpp). Returns {text, tokens, time, error}."""
    import urllib.request

    if backend == "sglang":
        formatted = GPT_OSS_TEMPLATE.format(system=SYSTEM_MSG, user=prompt)
        payload = json.dumps({
            "text": formatted,
            "sampling_params": {
                "max_new_tokens": max_tokens,
                "temperature": temperature,
                "stop": ["<|end|>"],
            },
        }).encode("utf-8")
        api_url = f"{url}/generate"
    else:
        payload = json.dumps({
            "model": "gpt-oss",
            "messages": [
                {"role": "system", "content": SYSTEM_MSG},
                {"role": "user", "content": prompt},
            ],
            "max_tokens": max_tokens,
            "temperature": temperature,
        }).encode("utf-8")
        api_url = f"{url}/v1/chat/completions"

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

    if backend == "sglang":
        text = result.get("text", "")
        meta = result.get("meta_info", {})
        tokens = meta.get("completion_tokens", 0)
        prompt_tokens = meta.get("prompt_tokens", 0)
    else:
        choices = result.get("choices", [])
        text = choices[0].get("message", {}).get("content", "") if choices else ""
        usage = result.get("usage", {})
        tokens = usage.get("completion_tokens", 0)
        prompt_tokens = usage.get("prompt_tokens", 0)

    return {"text": text, "tokens": tokens, "prompt_tokens": prompt_tokens,
            "time": round(elapsed, 2)}


# ---------------------------------------------------------------------------
# Single problem
# ---------------------------------------------------------------------------

def run_problem(problem_name: str, inputs_dir: Path, output_dir: Path,
                backend: str, url: str, temperature: float = 0.7) -> dict:
    """Run placeholder benchmark on one problem."""
    problem_input = inputs_dir / problem_name
    meta = json.loads((problem_input / "meta.json").read_text())
    source_path = problem_input / "stripped.dfy"

    # We need the original source to create placeholders (stripped.dfy has
    # assertions already removed; we need to re-read the verified code and
    # create placeholders from the essential assertion locations)
    # Actually, we can reconstruct from meta: we know the original code and
    # which assertions were essential. Let's use the original_code from meta.
    original_code = meta.get("original_code", "")
    if not original_code:
        return {"problem": problem_name, "error": "no original_code in meta"}

    # Write original to temp for placeholder generation
    tmp_src = Path("/tmp") / f"placeholder_{problem_name}.dfy"
    tmp_src.write_text(original_code)

    essential = meta.get("essential_assertions", [])
    placeholder_code, placeholders = make_placeholder_code(tmp_src, essential)
    tmp_src.unlink()

    if not placeholders:
        return {"problem": problem_name, "error": "no placeholders generated"}

    # Setup output
    problem_out = output_dir / problem_name
    problem_out.mkdir(parents=True, exist_ok=True)
    tmp_dir = problem_out / "tmp"
    tmp_dir.mkdir(exist_ok=True)

    # Save placeholder code for reference
    (problem_out / "placeholder_code.dfy").write_text(placeholder_code)
    (problem_out / "placeholders.json").write_text(json.dumps(placeholders, indent=2))

    result = {
        "problem": problem_name,
        "essential_count": len(placeholders),
        "backend": backend,
        "model": "gpt-oss-20b",
        "mode": "placeholder",
        "temperature": temperature,
        "start_time": datetime.now().isoformat(),
        "attempts": [],
        "success": False,
        "total_time": 0,
        "total_tokens": 0,
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

        prompt = build_prompt(placeholder_code, placeholders, dafny_error, attempt)
        attempt_data["prompt_length"] = len(prompt)

        print(f"  [{problem_name}] Attempt {attempt}...")
        llm_result = call_llm(url, prompt, backend, temperature=temperature)

        attempt_data["llm_response"] = llm_result["text"]
        attempt_data["llm_tokens"] = llm_result.get("tokens", 0)
        attempt_data["llm_time"] = llm_result.get("time", 0)
        result["total_tokens"] += llm_result.get("tokens", 0)

        if llm_result.get("error"):
            print(f"  [{problem_name}] LLM error: {llm_result['error'][:200]}")
            attempt_data["error"] = llm_result["error"]
            result["attempts"].append(attempt_data)
            time.sleep(5)
            continue

        # Parse assertions from response
        assertions = parse_assertions(llm_result["text"], len(placeholders))
        attempt_data["parsed_assertions"] = assertions

        if not assertions:
            print(f"  [{problem_name}] Could not parse assertions from response")
            attempt_data["dafny_success"] = False
            attempt_data["dafny_output"] = "PARSE_FAILED"
            result["attempts"].append(attempt_data)
            dafny_error = "Could not parse your response as a JSON array. Output ONLY a JSON array like: [{\"id\": 0, \"assertion\": \"assert ...;\"}]"
            continue

        # Fill placeholders and verify
        filled_code = fill_placeholders(placeholder_code, assertions, placeholders)
        attempt_data["filled_code"] = filled_code

        success, dafny_output, verify_time = run_dafny(filled_code, tmp_dir)
        attempt_data["dafny_success"] = success
        attempt_data["dafny_output"] = dafny_output
        attempt_data["dafny_time"] = verify_time

        # Per-assertion comparison with ground truth
        matches = []
        for p, a in zip(placeholders, assertions):
            orig = p["original_text"].strip().rstrip(";")
            guess = a.strip().rstrip(";") if a else ""
            # Normalize: strip "assert " prefix for comparison
            orig_expr = re.sub(r'^assert\s+', '', orig)
            guess_expr = re.sub(r'^assert\s+', '', guess)
            matches.append({
                "id": p["id"],
                "original": p["original_text"],
                "guess": a,
                "exact_match": orig_expr == guess_expr,
            })
        attempt_data["assertion_matches"] = matches

        result["attempts"].append(attempt_data)

        if success:
            print(f"  [{problem_name}] VERIFIED on attempt {attempt}!")
            result["success"] = True
            result["verified_code"] = filled_code
            result["final_assertions"] = assertions
            exact = sum(1 for m in matches if m["exact_match"])
            print(f"    Exact matches: {exact}/{len(matches)}")
            break
        else:
            error_lines = [l for l in dafny_output.split("\n")
                          if "Error" in l or "error" in l or "could not be proved" in l]
            dafny_error = "\n".join(error_lines[:10]) if error_lines else dafny_output[:500]
            print(f"  [{problem_name}] Attempt {attempt} failed ({verify_time}s)")

    result["total_time"] = round(time.perf_counter() - t_start, 2)
    result["total_attempts"] = attempt
    result["end_time"] = datetime.now().isoformat()

    (problem_out / "result.json").write_text(json.dumps(result, indent=2, default=str))

    status = "PASS" if result["success"] else "FAIL"
    print(f"  [{problem_name}] {status} ({attempt} attempts, {result['total_time']}s, {result['total_tokens']} tokens)")
    return result


# ---------------------------------------------------------------------------
# Main
# ---------------------------------------------------------------------------

def main():
    parser = argparse.ArgumentParser(description="Placeholder assertion benchmark")
    parser.add_argument("--inputs-dir", type=str, required=True)
    parser.add_argument("--output-dir", type=str, default="benchmark_results_placeholder")
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

    print(f"Placeholder benchmark: {len(names)} problems, backend={args.backend}")
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
        "mode": "placeholder",
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
    print(f"PLACEHOLDER BENCHMARK COMPLETE")
    print(f"{'='*60}")
    print(f"Problems: {len(all_results)}")
    print(f"Success:  {successes}/{len(all_results)} ({summary['success_rate']}%)")
    print(f"Time:     {total_time}s")
    print(f"Results:  {output_dir}/summary.json")


if __name__ == "__main__":
    main()

#!/usr/bin/env python3
from __future__ import annotations
"""
Benchmark LLMs on simplified minimal quirk examples.

For each quirk type, gives the LLM the stripped code (assertion removed)
and asks it to add the missing assertion. Much faster than the full
benchmark — only 6 tiny programs (8-20 lines each).

Usage:
    python3 benchmark_simplified.py --url http://127.0.0.1:8000 --backend sglang
    python3 benchmark_simplified.py --url http://127.0.0.1:8000 --backend sglang --types B1-take-full
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

SCRIPT_DIR = Path(__file__).parent.resolve()
EXAMPLES_DIR = SCRIPT_DIR / "examples"

DOTNET = os.environ.get("DOTNET8", os.environ.get("DOTNET", "dotnet"))
DAFNY_DLL = os.environ.get("DAFNY_DLL", "Dafny.dll")
Z3_PATH = os.environ.get("Z3_PATH", None)
TIMEOUT_PER_TYPE = 300  # seconds
MAX_TOKENS = 8192  # reasoning models need budget for thinking + code
VERIFY_TIMEOUT = 30

SYSTEM_MSG = "You are a Dafny verification expert. Output only code, no explanations."

_CHAT_API = os.environ.get("BENCHMARK_CHAT_API", "false").lower() == "true"
_CHAT_TEMPLATE = os.environ.get("BENCHMARK_CHAT_TEMPLATE", (
    "<|start|>system<|message|>{system}<|end|>"
    "<|start|>user<|message|>{user}<|end|>"
    "<|start|>assistant<|channel|>final<|message|>"
))
_EXTRA_STOP = os.environ.get("BENCHMARK_STOP_TOKENS", "").split("|")
_EXTRA_STOP = [s for s in _EXTRA_STOP if s]


# ---------------------------------------------------------------------------
# LLM call (same as main benchmark)
# ---------------------------------------------------------------------------

def call_llm(url: str, prompt: str, backend: str,
             max_tokens: int = MAX_TOKENS, temperature: float = 0.7) -> dict:
    import urllib.request

    if backend == "sglang" and not _CHAT_API:
        formatted = _CHAT_TEMPLATE.format(system=SYSTEM_MSG, user=prompt)
        payload = json.dumps({
            "text": formatted,
            "sampling_params": {
                "max_new_tokens": max_tokens,
                "temperature": temperature,
                "stop": ["</DAFNY_CODE>"] + _EXTRA_STOP,
            },
        }).encode("utf-8")
        api_url = f"{url}/generate"
    else:
        payload = json.dumps({
            "model": "default",
            "messages": [
                {"role": "system", "content": SYSTEM_MSG},
                {"role": "user", "content": prompt},
            ],
            "max_tokens": max_tokens,
            "temperature": temperature,
            "stop": ["</DAFNY_CODE>"] + _EXTRA_STOP,
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

    reasoning = ""

    if backend == "sglang" and not _CHAT_API:
        raw_text = result.get("text", "")
        # Extract reasoning from <|channel|>analysis sections
        import re as _re
        analysis_match = _re.search(r'<\|channel\|>analysis<\|message\|>(.*?)(?:<\|channel\|>|<\|end\|>|$)',
                                     raw_text, _re.DOTALL)
        if analysis_match:
            reasoning = analysis_match.group(1).strip()
        # Extract final content
        final_match = _re.search(r'<\|channel\|>final<\|message\|>(.*?)(?:<\|end\|>|$)',
                                  raw_text, _re.DOTALL)
        text = final_match.group(1).strip() if final_match else raw_text
        meta = result.get("meta_info", {})
        tokens = meta.get("completion_tokens", 0)
        prompt_tokens = meta.get("prompt_tokens", 0)
    else:
        choices = result.get("choices", [])
        msg = choices[0].get("message", {}) if choices else {}
        text = msg.get("content", "")
        reasoning = msg.get("reasoning_content", "")
        usage = result.get("usage", {})
        tokens = usage.get("completion_tokens", 0)
        prompt_tokens = usage.get("prompt_tokens", 0)

    return {"text": text, "reasoning": reasoning,
            "tokens": tokens, "prompt_tokens": prompt_tokens,
            "time": round(elapsed, 2)}


# ---------------------------------------------------------------------------
# Code extraction + verification
# ---------------------------------------------------------------------------

def extract_code(response: str, stripped_code: str | None = None) -> str | None:
    """Extract code from LLM response. If the response is just an assertion,
    insert it into the stripped code at the placeholder location."""
    # Strategy 1: DAFNY_CODE tags or markdown
    for pattern in [r'<DAFNY_CODE>\s*(.*?)(?:</DAFNY_CODE>|$)',
                    r'```dafny\s*(.*?)\s*```', r'```\s*(.*?)\s*```']:
        m = re.search(pattern, response, re.DOTALL | re.IGNORECASE)
        if m:
            return m.group(1).strip()

    # Strategy 2: Full program in response
    if "method " in response or "function " in response or "lemma " in response:
        return response.strip()

    # Strategy 3: Response contains just an assert statement — insert into stripped code
    if stripped_code:
        # Find placeholder lines in stripped code
        removed_lines = [l for l in stripped_code.split("\n") if "// TODO: add assertion here" in l]

        # Find assert statements in the response
        assertions = []
        for line in response.split("\n"):
            line = line.strip()
            if line.startswith("assert ") and ";" in line:
                assertions.append(line)
        if not assertions:
            m = re.search(r'(assert\s+.+?;)', response)
            if m:
                assertions.append(m.group(1))

        if assertions and removed_lines:
            result = stripped_code
            for removed_line, assertion in zip(removed_lines, assertions):
                indent = len(removed_line) - len(removed_line.lstrip())
                result = result.replace(removed_line, " " * indent + assertion, 1)
            if result != stripped_code:
                return result

    return None


def verify(code: str, tmp_dir: Path) -> tuple[bool, str, float]:
    dfy = tmp_dir / "attempt.dfy"
    dfy.write_text(code)
    cmd = [DOTNET, str(DAFNY_DLL), "verify", str(dfy),
           "--verification-time-limit", str(VERIFY_TIMEOUT)]
    if Z3_PATH:
        cmd.extend(["--solver-path", Z3_PATH])
    t0 = time.perf_counter()
    try:
        r = subprocess.run(cmd, capture_output=True, text=True, timeout=VERIFY_TIMEOUT + 30)
        output = r.stdout + "\n" + r.stderr
    except (subprocess.TimeoutExpired, FileNotFoundError) as e:
        output = str(e)
    elapsed = time.perf_counter() - t0
    return "0 errors" in output, output.strip(), round(elapsed, 2)


# ---------------------------------------------------------------------------
# Prompt
# ---------------------------------------------------------------------------

def build_prompt(stripped_code: str, type_name: str, description: str,
                 dafny_error: str | None = None, attempt: int = 1) -> str:
    if attempt == 1 or not dafny_error:
        return f"""This short Dafny program fails verification because one `assert` statement was removed.
The missing assertion is of type: {description}

Add the missing `assert` statement to make `dafny verify` pass.
Do NOT modify any existing code — only add one assert.
Return the complete program inside <DAFNY_CODE> tags.

```dafny
{stripped_code}
```

<DAFNY_CODE>
"""
    else:
        return f"""Your previous assertion was wrong. Error:
{dafny_error}

The program (unchanged):
```dafny
{stripped_code}
```

Add the correct `assert` to make it verify. Return inside <DAFNY_CODE> tags.

<DAFNY_CODE>
"""


# ---------------------------------------------------------------------------
# Run one type
# ---------------------------------------------------------------------------

def run_type(type_name: str, example_dir: Path, output_dir: Path,
             backend: str, url: str, temperature: float) -> dict:
    meta = json.loads((example_dir / "meta.json").read_text())
    stripped = (example_dir / "stripped.dfy").read_text()
    original = (example_dir / "example.dfy").read_text()

    out = output_dir / type_name
    out.mkdir(parents=True, exist_ok=True)
    tmp = out / "tmp"
    tmp.mkdir(exist_ok=True)

    result = {
        "type": type_name,
        "description": meta.get("description", ""),
        "original_assertion": meta.get("source_assertion", ""),
        "lines_of_code": meta.get("lines_of_code", 0),
        "model": os.environ.get("BENCHMARK_MODEL", "unknown"),
        "backend": backend,
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
        elapsed = time.perf_counter() - t_start
        if elapsed >= TIMEOUT_PER_TYPE:
            break

        attempt += 1
        ad = {"attempt": attempt, "start_time": datetime.now().isoformat()}

        prompt = build_prompt(stripped, type_name, meta.get("description", ""),
                              dafny_error, attempt)
        ad["prompt_length"] = len(prompt)

        print(f"  [{type_name}] Attempt {attempt}...")
        llm = call_llm(url, prompt, backend, temperature=temperature)

        ad["llm_response"] = llm["text"]
        ad["llm_reasoning"] = llm.get("reasoning", "")
        ad["llm_tokens"] = llm.get("tokens", 0)
        ad["llm_time"] = llm.get("time", 0)
        result["total_tokens"] += llm.get("tokens", 0)

        if llm.get("error"):
            print(f"  [{type_name}] LLM error: {llm['error'][:100]}")
            ad["error"] = llm["error"]
            result["attempts"].append(ad)
            time.sleep(5)
            continue

        code = extract_code(llm["text"], stripped)
        ad["extracted_code"] = code

        if not code:
            print(f"  [{type_name}] No code extracted")
            ad["dafny_success"] = False
            result["attempts"].append(ad)
            dafny_error = "Could not extract code. Return the complete program inside <DAFNY_CODE> tags."
            time.sleep(2)
            continue

        ok, output, vtime = verify(code, tmp)
        ad["dafny_success"] = ok
        ad["dafny_output"] = output
        ad["dafny_time"] = vtime

        # Check if the added assertion matches the original type
        ad["assertion_added"] = None
        code_lines = code.split("\n")
        orig_lines = set(original.split("\n"))
        for line in code_lines:
            if line not in orig_lines and line.strip().startswith("assert "):
                ad["assertion_added"] = line.strip()
                break

        # Exact match with ground truth
        orig_assertion = meta.get("source_assertion", "").strip()
        added = ad.get("assertion_added") or ""
        ad["exact_match"] = (added.rstrip(";").strip()
                             == orig_assertion.rstrip(";").strip())

        result["attempts"].append(ad)

        if ok:
            print(f"  [{type_name}] VERIFIED on attempt {attempt}!")
            if ad.get("assertion_added"):
                print(f"    Added: {ad['assertion_added']}")
                print(f"    Exact match: {ad['exact_match']}")
            result["success"] = True
            result["verified_code"] = code
            result["assertion_added"] = ad.get("assertion_added")
            result["exact_match"] = ad.get("exact_match", False)
            break
        else:
            errors = [l for l in output.split("\n")
                      if "Error" in l or "error" in l or "could not be proved" in l]
            dafny_error = "\n".join(errors[:5]) if errors else output[:300]
            print(f"  [{type_name}] Failed ({vtime}s)")

    result["total_time"] = round(time.perf_counter() - t_start, 2)
    result["total_attempts"] = attempt
    result["end_time"] = datetime.now().isoformat()

    (out / "result.json").write_text(json.dumps(result, indent=2, default=str))

    status = "PASS" if result["success"] else "FAIL"
    print(f"  [{type_name}] {status} ({attempt} att, {result['total_time']}s, {result['total_tokens']} tok)")
    return result


# ---------------------------------------------------------------------------
# Main
# ---------------------------------------------------------------------------

def main():
    parser = argparse.ArgumentParser(description="Benchmark LLM on simplified quirk examples")
    parser.add_argument("--url", required=True, help="LLM server URL")
    parser.add_argument("--backend", choices=["sglang", "llama"], default="sglang")
    parser.add_argument("--output-dir", default=None, help="Results directory")
    parser.add_argument("--types", nargs="+", help="Specific types to benchmark")
    parser.add_argument("--temperature", type=float, default=0.7)
    parser.add_argument("--timeout", type=int, default=300)
    parser.add_argument("--run-id", default=None, help="Run number (for repeated runs)")
    args = parser.parse_args()

    global TIMEOUT_PER_TYPE
    TIMEOUT_PER_TYPE = args.timeout

    model = os.environ.get("BENCHMARK_MODEL", "unknown")
    if not args.output_dir:
        suffix = f"_run{args.run_id}" if args.run_id else ""
        args.output_dir = str(SCRIPT_DIR / "results" / f"{model}{suffix}")

    output_dir = Path(args.output_dir)
    output_dir.mkdir(parents=True, exist_ok=True)

    # Find all example types
    types = []
    for d in sorted(EXAMPLES_DIR.iterdir()):
        if d.is_dir() and (d / "example.dfy").exists():
            types.append(d.name)

    if args.types:
        types = [t for t in types if t in args.types]

    print(f"Simplified benchmark: {len(types)} types, model={model}, backend={args.backend}")
    print(f"Types: {', '.join(types)}")
    print()

    t0 = time.perf_counter()
    all_results = []

    for type_name in types:
        r = run_type(type_name, EXAMPLES_DIR / type_name, output_dir,
                     args.backend, args.url, args.temperature)
        all_results.append(r)

    total_time = round(time.perf_counter() - t0, 1)
    successes = sum(1 for r in all_results if r.get("success"))
    exact = sum(1 for r in all_results if r.get("exact_match"))

    summary = {
        "timestamp": datetime.now().isoformat(),
        "model": model,
        "backend": args.backend,
        "total_types": len(all_results),
        "successes": successes,
        "exact_matches": exact,
        "success_rate": round(100 * successes / len(all_results), 1) if all_results else 0,
        "total_time": total_time,
        "total_tokens": sum(r.get("total_tokens", 0) for r in all_results),
        "per_type": [
            {
                "type": r["type"],
                "success": r.get("success", False),
                "exact_match": r.get("exact_match", False),
                "attempts": r.get("total_attempts", 0),
                "time": r.get("total_time", 0),
                "tokens": r.get("total_tokens", 0),
                "assertion_added": r.get("assertion_added"),
            }
            for r in all_results
        ],
    }
    (output_dir / "summary.json").write_text(json.dumps(summary, indent=2))

    print(f"\n{'='*60}")
    print(f"SIMPLIFIED BENCHMARK — {model}")
    print(f"{'='*60}")
    print(f"Types: {len(all_results)}  Pass: {successes}  Exact: {exact}  Rate: {summary['success_rate']}%")
    print(f"Time: {total_time}s  Tokens: {summary['total_tokens']}")
    for r in all_results:
        status = "PASS" if r.get("success") else "FAIL"
        em = " (exact)" if r.get("exact_match") else ""
        print(f"  {r['type']}: {status}{em} — {r.get('assertion_added', 'none')}")


if __name__ == "__main__":
    main()

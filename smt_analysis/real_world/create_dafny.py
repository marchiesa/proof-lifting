#!/usr/bin/env python3
"""Create minimal Dafny programs from CodeSearchNet candidates.

For each candidate:
1. Extract the algorithmic gist (core pattern)
2. Create a minimal Dafny program (10-20 lines) with spec
3. Try to verify it
4. If verification fails, add assertions until it passes
5. Record which assertions were needed (potential SMT quirks)

Usage:
    python3 create_dafny.py                    # process all candidates
    python3 create_dafny.py --start 0 --end 10 # process candidates 0-9
    python3 create_dafny.py --id 5             # process single candidate
"""
from __future__ import annotations

import argparse
import json
import os
import re
import subprocess
import sys
import time
from pathlib import Path

SCRIPT_DIR = Path(__file__).parent.resolve()
CANDIDATES_PATH = SCRIPT_DIR / "candidates.json"
OUTPUT_DIR = SCRIPT_DIR / "programs"

DOTNET = os.environ.get("DOTNET8", os.environ.get("DOTNET", "dotnet"))
DAFNY_DLL = os.environ.get("DAFNY_DLL",
    "/Users/mchiesa/work/projects/2026-02-dafny-liftings/dafny-source/Binaries/Dafny.dll")
Z3_PATH = os.environ.get("Z3_PATH", None)
VERIFY_TIMEOUT = 30


def verify_dafny(code: str, tmp_dir: Path) -> tuple[bool, str]:
    """Verify a Dafny program. Returns (success, output)."""
    dfy = tmp_dir / "program.dfy"
    dfy.write_text(code)
    cmd = [DOTNET, str(DAFNY_DLL), "verify", str(dfy),
           "--verification-time-limit", str(VERIFY_TIMEOUT)]
    if Z3_PATH:
        cmd.extend(["--solver-path", Z3_PATH])
    try:
        r = subprocess.run(cmd, capture_output=True, text=True, timeout=VERIFY_TIMEOUT + 30)
        output = r.stdout + "\n" + r.stderr
    except (subprocess.TimeoutExpired, FileNotFoundError) as e:
        output = str(e)
    return "0 errors" in output, output.strip()


SYSTEM_PROMPT = """You are a Dafny verification expert. Your task is to create a minimal
Dafny program inspired by a real-world Python function.

Rules:
1. Extract the CORE ALGORITHMIC PATTERN from the Python function
2. Create a Dafny method that captures this pattern in 10-20 lines
3. Add a natural specification (requires/ensures)
4. Add loop invariants so it verifies
5. The program should verify with `dafny verify`
6. Use only basic Dafny types: int, bool, seq<int>, seq<bool>, etc.
7. Do NOT use assume statements
8. The goal is a clean, minimal program — not a literal translation"""

def create_dafny_prompt(candidate: dict) -> str:
    """Create a prompt for generating a Dafny program from a candidate."""
    return f"""Here is a Python function from a real open-source project ({candidate['repo']}):

```python
{candidate['code']}
```

Docstring: {candidate['doc'][:200]}

Create a minimal Dafny program (10-20 lines) that captures the core algorithmic pattern.
The program should:
- Have a clear specification (ensures clause)
- Use a loop with invariants
- Verify with `dafny verify`

Return ONLY the Dafny code inside <DAFNY_CODE> tags. No explanations.

<DAFNY_CODE>
"""


def create_dafny_fix_prompt(candidate: dict, code: str, error: str) -> str:
    """Create a prompt for fixing a Dafny verification error."""
    return f"""This Dafny program inspired by {candidate['repo']}/{candidate['name']} fails verification:

```dafny
{code}
```

Error:
{error[:500]}

Fix the program so it verifies. You may add assertions, fix invariants, or adjust the spec.
Do NOT use assume statements. Return ONLY the fixed code inside <DAFNY_CODE> tags.

<DAFNY_CODE>
"""


def extract_code(response: str) -> str | None:
    """Extract Dafny code from response."""
    for pattern in [r'<DAFNY_CODE>\s*(.*?)(?:</DAFNY_CODE>|$)',
                    r'```dafny\s*(.*?)\s*```', r'```\s*(.*?)\s*```']:
        m = re.search(pattern, response, re.DOTALL | re.IGNORECASE)
        if m:
            return m.group(1).strip()
    return None


def call_claude(prompt: str, system: str = SYSTEM_PROMPT) -> str:
    """Call Claude CLI to get a response."""
    # Use subprocess to call claude CLI
    full_prompt = f"{system}\n\n{prompt}"
    try:
        r = subprocess.run(
            ["claude", "-p", full_prompt, "--no-input"],
            capture_output=True, text=True, timeout=120
        )
        return r.stdout.strip()
    except (subprocess.TimeoutExpired, FileNotFoundError) as e:
        return f"ERROR: {e}"


def process_candidate(candidate: dict, output_dir: Path) -> dict:
    """Process a single candidate: create Dafny program, verify, iterate."""
    cid = candidate["id"]
    name = candidate["name"]
    quirk = candidate["quirk_type"]

    out = output_dir / f"{cid:04d}_{quirk}"
    out.mkdir(parents=True, exist_ok=True)
    tmp = out / "tmp"
    tmp.mkdir(exist_ok=True)

    result = {
        "id": cid,
        "repo": candidate["repo"],
        "path": candidate["path"],
        "name": name,
        "quirk_type": quirk,
        "gist": candidate["gist"],
        "url": candidate.get("url", ""),
        "attempts": [],
        "verified": False,
        "assertions_needed": [],
    }

    # Save source Python
    (out / "source.py").write_text(candidate["code"])
    (out / "meta.json").write_text(json.dumps({
        "repo": candidate["repo"],
        "path": candidate["path"],
        "name": name,
        "quirk_type": quirk,
        "gist": candidate["gist"],
        "doc": candidate["doc"],
        "url": candidate.get("url", ""),
    }, indent=2))

    # Generate initial Dafny program
    print(f"  [{cid}] Generating Dafny for {name} ({quirk})...")
    prompt = create_dafny_prompt(candidate)
    response = call_claude(prompt)
    code = extract_code(response)

    if not code:
        print(f"  [{cid}] No code extracted")
        result["error"] = "no_code_extracted"
        (out / "result.json").write_text(json.dumps(result, indent=2))
        return result

    result["attempts"].append({"code": code, "response": response[:500]})
    (out / "program_v0.dfy").write_text(code)

    # Try to verify, iterate up to 3 times
    for attempt in range(4):
        ok, output = verify_dafny(code, tmp)

        if ok:
            print(f"  [{cid}] VERIFIED on attempt {attempt}")
            result["verified"] = True
            result["final_code"] = code
            (out / "verified.dfy").write_text(code)
            break
        else:
            errors = [l for l in output.split("\n")
                      if "Error" in l or "error" in l or "could not be proved" in l]
            error_msg = "\n".join(errors[:5]) if errors else output[:300]
            result["attempts"][-1]["error"] = error_msg

            if attempt < 3:
                print(f"  [{cid}] Attempt {attempt} failed, fixing...")
                prompt = create_dafny_fix_prompt(candidate, code, error_msg)
                response = call_claude(prompt)
                new_code = extract_code(response)
                if new_code:
                    code = new_code
                    result["attempts"].append({"code": code, "response": response[:500]})
                    (out / f"program_v{attempt+1}.dfy").write_text(code)
                else:
                    print(f"  [{cid}] No code in fix response")
                    break

    if not result["verified"]:
        print(f"  [{cid}] FAILED after {len(result['attempts'])} attempts")

    # Count assertions in final code
    if result.get("final_code"):
        asserts = [l.strip() for l in result["final_code"].split("\n")
                   if l.strip().startswith("assert ")]
        result["assertions_needed"] = asserts
        result["n_assertions"] = len(asserts)

    (out / "result.json").write_text(json.dumps(result, indent=2, default=str))

    status = "VERIFIED" if result["verified"] else "FAILED"
    n_asserts = result.get("n_assertions", 0)
    print(f"  [{cid}] {status} — {n_asserts} assertions — {name}")

    return result


def main():
    parser = argparse.ArgumentParser(description="Create Dafny programs from candidates")
    parser.add_argument("--start", type=int, default=0)
    parser.add_argument("--end", type=int, default=None)
    parser.add_argument("--id", type=int, default=None)
    args = parser.parse_args()

    candidates = json.loads(CANDIDATES_PATH.read_text())
    print(f"Loaded {len(candidates)} candidates")

    OUTPUT_DIR.mkdir(parents=True, exist_ok=True)

    if args.id is not None:
        to_process = [c for c in candidates if c["id"] == args.id]
    else:
        end = args.end or len(candidates)
        to_process = candidates[args.start:end]

    print(f"Processing {len(to_process)} candidates (IDs {to_process[0]['id']}-{to_process[-1]['id']})")

    results = []
    for c in to_process:
        r = process_candidate(c, OUTPUT_DIR)
        results.append(r)

    # Summary
    verified = sum(1 for r in results if r["verified"])
    with_asserts = sum(1 for r in results if r.get("n_assertions", 0) > 0)
    print(f"\n{'='*60}")
    print(f"SUMMARY: {verified}/{len(results)} verified, {with_asserts} with assertions")
    print(f"{'='*60}")

    # Save summary
    summary = {
        "total": len(results),
        "verified": verified,
        "with_assertions": with_asserts,
        "results": [{
            "id": r["id"],
            "name": r["name"],
            "quirk_type": r["quirk_type"],
            "verified": r["verified"],
            "n_assertions": r.get("n_assertions", 0),
            "assertions": r.get("assertions_needed", []),
        } for r in results],
    }
    (OUTPUT_DIR / "summary.json").write_text(json.dumps(summary, indent=2))


if __name__ == "__main__":
    main()

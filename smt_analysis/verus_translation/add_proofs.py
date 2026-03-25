#!/usr/bin/env python3
"""Add proofs to translated Verus programs using Claude Code subagents.

For each translated program that doesn't verify:
1. Run verus to get errors
2. Send code + errors to Claude to add proofs (invariants, decreases, assertions)
3. Iterate until verified or max attempts reached

Usage:
    python3 add_proofs.py                    # all unverified programs
    python3 add_proofs.py --problem X        # specific problem
    python3 add_proofs.py --limit 5          # at most 5 programs
"""
from __future__ import annotations

import argparse
import json
import os
import re
import subprocess
import time
from pathlib import Path

SCRIPT_DIR = Path(__file__).parent.resolve()
PROGRAMS_DIR = SCRIPT_DIR / "programs"
STATUS_FILE = SCRIPT_DIR / "status.json"
PROOF_STATUS_FILE = SCRIPT_DIR / "proof_status.json"
VERUS_BIN = os.environ.get("VERUS_BIN", "/tmp/verus_install/verus-arm64-macos/verus")
VERIFY_TIMEOUT = 60
MAX_ATTEMPTS = 5


def verify(rs_path: Path) -> tuple[bool, str]:
    """Run verus on a file. Returns (success, output)."""
    try:
        r = subprocess.run(
            [VERUS_BIN, str(rs_path)],
            capture_output=True, text=True, timeout=VERIFY_TIMEOUT
        )
        output = r.stdout + "\n" + r.stderr
        ok = r.returncode == 0 and "0 errors" in output
        return ok, output
    except subprocess.TimeoutExpired:
        return False, "TIMEOUT"
    except FileNotFoundError:
        return False, "verus binary not found"


def extract_errors(output: str) -> str:
    """Extract meaningful error lines from verus output."""
    lines = output.split("\n")
    errors = []
    for i, line in enumerate(lines):
        if "error" in line.lower() and not line.strip().startswith("//"):
            # Include some context
            errors.append(line.strip())
            # Get the next line if it has a caret or note
            if i + 1 < len(lines) and ("|" in lines[i+1] or "note:" in lines[i+1]):
                errors.append(lines[i+1].strip())
    return "\n".join(errors[:20]) if errors else output[:1000]


def call_claude(prompt: str) -> str:
    """Call Claude CLI."""
    try:
        r = subprocess.run(
            ["claude", "-p", "--dangerously-skip-permissions", "--no-session-persistence"],
            input=prompt, capture_output=True, text=True, timeout=300
        )
        return r.stdout.strip()
    except subprocess.TimeoutExpired:
        return "TIMEOUT"
    except FileNotFoundError:
        return "ERROR: claude not found"


def extract_code(response: str) -> str | None:
    """Extract Rust code from response."""
    for pattern in [r'```rust\s*(.*?)\s*```', r'```\s*(.*?)\s*```']:
        m = re.search(pattern, response, re.DOTALL)
        if m:
            return m.group(1).strip()
    if "use vstd" in response:
        idx = response.index("use vstd")
        return response[idx:].strip()
    if "verus!" in response:
        idx = response.index("verus!")
        prefix = response[:idx]
        use_idx = prefix.rfind("use ")
        if use_idx >= 0:
            return response[use_idx:].strip()
        return response[idx:].strip()
    return None


def build_initial_prompt(verus_code: str, dafny_code: str, errors: str, problem: str) -> str:
    return f"""This Verus (Rust verification) program compiles but does NOT verify.
Add the necessary proof annotations to make it verify with `verus`.

The program was translated from Dafny. Below is the VERIFIED Dafny version
with working proofs (loop invariants, assertions, lemmas). Use it as a direct
guide — translate the Dafny proof strategy to Verus. The specs may differ
slightly but the proof structure should be similar.

RULES FOR VERUS PROOFS:
1. Add `decreases` clauses to all loops (e.g., `decreases vec.len() - i`)
2. Add loop invariants with `invariant` keyword inside while loops
3. For sequence extensionality: use `assert(s.take(i+1).drop_last() =~= s.take(i));`
   This is the Verus equivalent of Dafny's `assert a[..i+1] == a[..i] + [a[i]]`
4. For take-full: use `assert(s.take(s.len() as int) =~= s);`
   This is the Verus equivalent of Dafny's `assert a[..|a|] == a`
5. Use `proof {{ ... }}` blocks for proof-only code inside exec functions
6. Use `assert(...)` for assertions
7. For triggers: add `#[trigger]` annotations on quantified expressions
8. Do NOT use `assume(false)` — replace with real proofs
9. Keep all `spec fn` definitions unchanged
10. Keep the method signature (requires/ensures) unchanged
11. If a ghost variable is needed, use `let ghost x = ...;`

Verus code ({problem}):
```rust
{verus_code}
```

VERIFIED Dafny (has working proofs — use as guide for invariants/assertions):
```dafny
{dafny_code}
```

Verus errors:
{errors[:1500]}

Output ONLY the fixed Rust/Verus code. No explanations. Start with `use vstd::prelude::*;`"""


def build_fix_prompt(verus_code: str, dafny_code: str, errors: str, problem: str) -> str:
    return f"""This Verus program still has verification errors. Fix them.

REMEMBER:
- `assert(s.take(i+1).drop_last() =~= s.take(i));` for sequence extensionality
- `assert(s.take(s.len() as int) =~= s);` for take-full
- Add proper `decreases` and `invariant` to loops
- Use `#[trigger]` for quantifier triggers
- Do NOT use `assume(false)`

Verus code:
```rust
{verus_code}
```

VERIFIED Dafny (working proofs — translate proof strategy to Verus):
```dafny
{dafny_code}
```

Errors:
{errors[:1500]}

Output ONLY the fixed Rust/Verus code. Start with `use vstd::prelude::*;`"""


def load_proof_status() -> dict:
    if PROOF_STATUS_FILE.exists():
        return json.loads(PROOF_STATUS_FILE.read_text())
    return {"verified": {}, "failed": {}, "in_progress": {}}


def save_proof_status(status: dict):
    PROOF_STATUS_FILE.write_text(json.dumps(status, indent=2))


def process_one(problem: str) -> dict:
    """Add proofs to one program."""
    rs_path = PROGRAMS_DIR / problem / "translated.rs"
    dfy_path = PROGRAMS_DIR / problem / "source.dfy"
    # Use the VERIFIED Dafny file (has working proofs) if available
    dfy_verified_path = SCRIPT_DIR.parent / "results" / problem / "verified.dfy"

    if not rs_path.exists():
        return {"status": "error", "error": "no translated.rs"}

    verus_code = rs_path.read_text()
    # Prefer verified.dfy (has proofs) over source.dfy (just spec)
    if dfy_verified_path.exists():
        dafny_code = dfy_verified_path.read_text()
    elif dfy_path.exists():
        dafny_code = dfy_path.read_text()
    else:
        dafny_code = ""

    # First check if it already verifies
    ok, output = verify(rs_path)
    if ok:
        return {"status": "already_verified", "attempts": 0}

    errors = extract_errors(output)
    print(f"  [{problem}] Initial errors: {errors[:100]}...")

    result = {"status": "in_progress", "attempts": []}

    for attempt in range(MAX_ATTEMPTS):
        print(f"  [{problem}] Attempt {attempt + 1}/{MAX_ATTEMPTS}...")

        if attempt == 0:
            prompt = build_initial_prompt(verus_code, dafny_code, errors, problem)
        else:
            prompt = build_fix_prompt(verus_code, dafny_code, errors, problem)

        response = call_claude(prompt)
        if response in ("TIMEOUT", "ERROR: claude not found"):
            result["attempts"].append({"error": response})
            continue

        new_code = extract_code(response)
        if not new_code:
            result["attempts"].append({"error": "no code extracted"})
            continue

        # Save attempt
        attempt_path = PROGRAMS_DIR / problem / f"proof_attempt_{attempt}.rs"
        attempt_path.write_text(new_code)
        result["attempts"].append({"code_length": len(new_code)})

        # Check if it compiles first (--no-verify)
        tmp_path = PROGRAMS_DIR / problem / "check_proof.rs"
        tmp_path.write_text(new_code)
        try:
            r = subprocess.run([VERUS_BIN, str(tmp_path), "--no-verify"],
                             capture_output=True, text=True, timeout=30)
            if r.returncode != 0:
                compile_err = extract_errors(r.stdout + "\n" + r.stderr)
                print(f"  [{problem}] Compile error, trying again...")
                errors = compile_err
                verus_code = new_code
                continue
        except:
            pass

        # Try verification
        ok, output = verify(tmp_path)
        if ok:
            print(f"  [{problem}] VERIFIED on attempt {attempt + 1}!")
            verified_path = PROGRAMS_DIR / problem / "verified.rs"
            verified_path.write_text(new_code)
            result["status"] = "verified"
            result["total_attempts"] = attempt + 1
            return result

        errors = extract_errors(output)
        verus_code = new_code
        print(f"  [{problem}] Still failing: {errors[:80]}...")

    result["status"] = "failed"
    result["total_attempts"] = MAX_ATTEMPTS
    result["last_error"] = errors[:500]
    return result


def main():
    import concurrent.futures
    import threading

    parser = argparse.ArgumentParser()
    parser.add_argument("--problem", nargs="+")
    parser.add_argument("--limit", type=int, default=None)
    parser.add_argument("--max-attempts", type=int, default=5)
    parser.add_argument("--workers", type=int, default=10, help="Parallel workers")
    args = parser.parse_args()

    global MAX_ATTEMPTS
    MAX_ATTEMPTS = args.max_attempts

    status = json.loads(STATUS_FILE.read_text())
    proof_status = load_proof_status()
    lock = threading.Lock()

    if args.problem:
        problems = args.problem
    else:
        # Get all translated programs that aren't already verified
        verif = json.loads((SCRIPT_DIR / "verification_results.json").read_text()) \
            if (SCRIPT_DIR / "verification_results.json").exists() else {"per_problem": {}}

        problems = []
        for p in sorted(status["translated"].keys()):
            vr = verif.get("per_problem", {}).get(p, {})
            if vr.get("result") != "verified" and p not in proof_status.get("verified", {}):
                problems.append(p)

    if args.limit:
        problems = problems[:args.limit]

    print(f"Adding proofs to {len(problems)} programs ({args.workers} workers, max {MAX_ATTEMPTS} attempts each)")
    print()

    completed = {"verified": 0, "failed": 0}

    def worker(problem):
        r = process_one(problem)
        with lock:
            if r["status"] in ("verified", "already_verified"):
                proof_status.setdefault("verified", {})[problem] = r
                completed["verified"] += 1
            else:
                proof_status.setdefault("failed", {})[problem] = r
                completed["failed"] += 1
            save_proof_status(proof_status)
            v = completed["verified"]
            f = completed["failed"]
            print(f"  Progress: {v} verified, {f} failed, {len(problems)-v-f} remaining")

    with concurrent.futures.ThreadPoolExecutor(max_workers=args.workers) as executor:
        futures = {executor.submit(worker, p): p for p in problems}
        concurrent.futures.wait(futures)

    # Summary
    v = len(proof_status.get("verified", {}))
    f = len(proof_status.get("failed", {}))
    print(f"\n{'='*60}")
    print(f"PROOF ADDITION SUMMARY")
    print(f"{'='*60}")
    print(f"Verified: {v}")
    print(f"Failed: {f}")


if __name__ == "__main__":
    main()

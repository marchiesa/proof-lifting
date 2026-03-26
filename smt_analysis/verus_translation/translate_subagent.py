#!/usr/bin/env python3
"""Translate verified Dafny programs to Verus using Claude Code subagents.

This is the recommended approach — achieves ~100% success rate by giving
each subagent the verified Dafny file (with working proofs) as reference
and letting it iterate with full tool access (read files, run verus, fix errors).

Usage:
    python3 translate_subagent.py                          # all remaining
    python3 translate_subagent.py --problems 0025_1096_A   # specific problems
    python3 translate_subagent.py --limit 5                # at most 5
    python3 translate_subagent.py --max-attempts 15        # more iterations

The script generates one prompt per problem and prints it. You then copy
these prompts into Claude Code Agent calls. For automation, use the
--generate-script flag to output a shell script that launches all agents.

Alternatively, use --run to directly call `claude -p` (less effective but
fully automated).
"""
from __future__ import annotations

import argparse
import json
import glob
import os
import subprocess
import re
import sys
from pathlib import Path

SCRIPT_DIR = Path(__file__).parent.resolve()
RESULTS_DIR = SCRIPT_DIR.parent / "results"
PROGRAMS_DIR = SCRIPT_DIR / "programs"
STATUS_FILE = SCRIPT_DIR / "subagent_status.json"
VERUS_BIN = os.environ.get("VERUS_BIN", "/tmp/verus_install/verus-arm64-macos/verus")
MAX_ATTEMPTS = 10


def get_verified_problems() -> list[str]:
    path = RESULTS_DIR / "verified_problems.txt"
    return [l.strip() for l in path.read_text().splitlines() if l.strip()]


def get_already_done() -> set[str]:
    """Get problems that already have a clean verified.rs (no assume(false))."""
    done = set()
    for f in PROGRAMS_DIR.glob("*/verified.rs"):
        code = f.read_text()
        if "assume(false)" not in code:
            done.add(f.parent.name)
    return done


def load_status() -> dict:
    if STATUS_FILE.exists():
        return json.loads(STATUS_FILE.read_text())
    return {"verified": {}, "failed": {}}


def save_status(status: dict):
    STATUS_FILE.write_text(json.dumps(status, indent=2))


def build_prompt(problem: str, max_attempts: int = 10) -> str:
    """Build the subagent prompt for a problem."""
    dfy_verified = RESULTS_DIR / problem / "verified.dfy"
    dfy_task = RESULTS_DIR / problem / "task.dfy"
    out_dir = PROGRAMS_DIR / problem
    out_file = out_dir / "full_translation.rs"
    verified_file = out_dir / "verified.rs"

    # Use verified.dfy if available
    source = str(dfy_verified) if dfy_verified.exists() else str(dfy_task)

    return f"""Translate this verified Dafny program to Verus (Rust verification tool).
Translate EVERYTHING including all proof bodies, lemmas, and assertions.
Do NOT use assume(false) anywhere.

Read the Dafny source at {source}

Verus translation rules:
- ghost function → spec fn
- ghost predicate → spec fn returning bool
- method → fn
- lemma → proof fn
- Use int/Seq<int> in spec mode, i64/Vec<i64> in exec mode
- a@.map(|_idx, x: i64| x as int) to convert Vec<i64> to Seq<int>
- forall i | cond :: body → forall|i: int| cond ==> body
- exists i | cond :: body → exists|i: int| cond && body
- s[..n] → s.take(n), s[n..] → s.skip(n), |s| → s.len()
- assert a[..i+1] == a[..i] + [a[i]] → assert(s.take(i+1).drop_last() =~= s.take(i))
- assert a[..|a|] == a → assert(s.take(s.len() as int) =~= s)
- Use by(nonlinear_arith) for nonlinear arithmetic
- Use reveal_with_fuel(fn_name, N) for recursive spec function unfolding
- Use #[trigger] annotations on quantified expressions
- Use proof {{ }} blocks for ghost reasoning in exec functions
- Add decreases clauses to all loops
- Wrap in verus! {{ }}, add use vstd::prelude::*; and fn main() {{}}

Write the complete translated file to {out_file}
Run: {VERUS_BIN} {out_file}
If it fails, read the errors and fix. Iterate until it verifies or you've tried {max_attempts} times.
If it verifies, copy the file to {verified_file}"""


def verify_file(rs_path: Path) -> tuple[bool, str]:
    """Run verus on a file."""
    try:
        r = subprocess.run(
            [VERUS_BIN, str(rs_path)],
            capture_output=True, text=True, timeout=120
        )
        output = r.stdout + "\n" + r.stderr
        return r.returncode == 0 and "0 errors" in output, output
    except Exception as e:
        return False, str(e)


def run_with_claude_p(problem: str, max_attempts: int) -> dict:
    """Run translation using claude -p (automated but less effective)."""
    dfy_verified = RESULTS_DIR / problem / "verified.dfy"
    dfy_task = RESULTS_DIR / problem / "task.dfy"
    source = dfy_verified if dfy_verified.exists() else dfy_task
    if not source.exists():
        return {"status": "error", "error": "no source"}

    dafny_code = source.read_text()
    out_dir = PROGRAMS_DIR / problem
    out_dir.mkdir(parents=True, exist_ok=True)

    prompt = f"""Translate this verified Dafny program to Verus (Rust verification tool).
Translate EVERYTHING including all proof bodies. No assume(false).
ghost function→spec fn, ghost predicate→spec fn bool, method→fn, lemma→proof fn.
int/Seq<int> in spec, i64/Vec<i64> in exec. by(nonlinear_arith) for NLA.
#[trigger] for quantifiers. reveal_with_fuel for recursive spec fns.
assert(s.take(i+1).drop_last() =~= s.take(i)) for extensionality.
Wrap in verus!{{}}, use vstd::prelude::*;, fn main(){{}}

Dafny source ({problem}):
```dafny
{dafny_code}
```

Output ONLY Rust/Verus code. Start with `use vstd::prelude::*;`"""

    for attempt in range(max_attempts):
        print(f"  [{problem}] Attempt {attempt + 1}/{max_attempts}...")
        try:
            r = subprocess.run(
                ["claude", "-p", "--dangerously-skip-permissions", "--no-session-persistence"],
                input=prompt, capture_output=True, text=True, timeout=300
            )
            response = r.stdout.strip()
        except Exception as e:
            continue

        # Extract code
        code = None
        for pattern in [r'```rust\s*(.*?)\s*```', r'```\s*(.*?)\s*```']:
            m = re.search(pattern, response, re.DOTALL)
            if m:
                code = m.group(1).strip()
                break
        if not code and "use vstd" in response:
            code = response[response.index("use vstd"):].strip()
        if not code:
            continue

        # Check for assume(false)
        if "assume(false)" in code:
            print(f"  [{problem}] Contains assume(false), rejecting...")
            continue

        rs_path = out_dir / "full_translation.rs"
        rs_path.write_text(code)

        ok, output = verify_file(rs_path)
        if ok:
            (out_dir / "verified.rs").write_text(code)
            return {"status": "verified", "attempts": attempt + 1}

        # Feed error back
        errors = "\n".join(l for l in output.split("\n") if "error" in l.lower())[:1000]
        prompt = f"""Fix this Verus program. Errors:
{errors}

Code:
```rust
{code}
```

Dafny reference:
```dafny
{dafny_code}
```

No assume(false). Output ONLY fixed Rust/Verus code."""

    return {"status": "failed", "attempts": max_attempts}


def main():
    parser = argparse.ArgumentParser(description="Translate Dafny to Verus via subagents")
    parser.add_argument("--problems", nargs="+", help="Specific problems")
    parser.add_argument("--limit", type=int, default=None)
    parser.add_argument("--max-attempts", type=int, default=10)
    parser.add_argument("--print-prompts", action="store_true",
                        help="Print prompts for manual Agent use")
    parser.add_argument("--run", action="store_true",
                        help="Run with claude -p (automated, less effective)")
    parser.add_argument("--workers", type=int, default=10,
                        help="Parallel workers for --run mode")
    args = parser.parse_args()

    already_done = get_already_done()

    if args.problems:
        problems = args.problems
    else:
        all_verified = get_verified_problems()
        problems = [p for p in all_verified if p not in already_done]

    if args.limit:
        problems = problems[:args.limit]

    print(f"Problems to translate: {len(problems)}")
    print(f"Already done (clean verified.rs): {len(already_done)}")
    print()

    if args.print_prompts:
        for p in problems:
            print(f"=== {p} ===")
            print(build_prompt(p, args.max_attempts))
            print()
        return

    if args.run:
        import concurrent.futures
        import threading

        status = load_status()
        lock = threading.Lock()

        def worker(problem):
            r = run_with_claude_p(problem, args.max_attempts)
            with lock:
                if r["status"] == "verified":
                    status["verified"][problem] = r
                else:
                    status["failed"][problem] = r
                save_status(status)
                v = len(status["verified"])
                f = len(status["failed"])
                print(f"  Progress: {v} verified, {f} failed")

        with concurrent.futures.ThreadPoolExecutor(max_workers=args.workers) as executor:
            futures = {executor.submit(worker, p): p for p in problems}
            concurrent.futures.wait(futures)

        v = len(status["verified"])
        f = len(status["failed"])
        print(f"\nDone. Verified: {v}, Failed: {f}")
    else:
        # Default: print prompts for manual Agent use
        print("Use --print-prompts to see prompts or --run to automate with claude -p")
        print()
        print("Recommended: launch Agent subagents manually from Claude Code:")
        print()
        for p in problems[:5]:
            print(f"  Agent(prompt=<prompt for {p}>, run_in_background=True)")
        if len(problems) > 5:
            print(f"  ... and {len(problems) - 5} more")


if __name__ == "__main__":
    main()

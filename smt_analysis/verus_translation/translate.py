#!/usr/bin/env python3
"""Translate Dafny programs (task.dfy) to Verus (Rust).

Uses Claude Code subagent to translate each program. Tracks progress
in status.json and saves results to per-problem directories.

Usage:
    python3 translate.py                           # translate all, starting from shortest
    python3 translate.py --problems 0025_1096_A    # translate specific problem(s)
    python3 translate.py --max-lines 50            # only problems under 50 lines
    python3 translate.py --limit 5                 # translate at most 5 problems
"""
from __future__ import annotations

import argparse
import json
import os
import subprocess
import sys
import time
from pathlib import Path

SCRIPT_DIR = Path(__file__).parent.resolve()
RESULTS_DIR = SCRIPT_DIR.parent / "results"
OUTPUT_DIR = SCRIPT_DIR / "programs"
STATUS_FILE = SCRIPT_DIR / "status.json"
VERUS_BIN = os.environ.get("VERUS_BIN", "/tmp/verus_install/verus-arm64-macos/verus")


def get_verified_problems() -> list[str]:
    """Get list of verified problem names."""
    path = RESULTS_DIR / "verified_problems.txt"
    return [l.strip() for l in path.read_text().splitlines() if l.strip()]


def get_line_count(problem: str) -> int:
    """Get line count for a problem's task.dfy."""
    task = RESULTS_DIR / problem / "task.dfy"
    if task.exists():
        return len(task.read_text().splitlines())
    return 999


def load_status() -> dict:
    """Load translation status."""
    if STATUS_FILE.exists():
        return json.loads(STATUS_FILE.read_text())
    return {"translated": {}, "failed": {}, "skipped": {}}


def save_status(status: dict):
    """Save translation status."""
    STATUS_FILE.write_text(json.dumps(status, indent=2))


def translate_one(problem: str, max_attempts: int = 3) -> dict:
    """Translate a single Dafny problem to Verus using Claude Code subagent."""
    task_path = RESULTS_DIR / problem / "task.dfy"
    verified_path = RESULTS_DIR / problem / "verified.dfy"

    # Use verified.dfy if available (has assertions), else task.dfy
    source_path = verified_path if verified_path.exists() else task_path
    if not source_path.exists():
        return {"status": "error", "error": "no source file"}

    dafny_code = source_path.read_text()
    line_count = len(dafny_code.splitlines())

    # Create output directory
    out_dir = OUTPUT_DIR / problem
    out_dir.mkdir(parents=True, exist_ok=True)

    # Save the source Dafny for reference
    (out_dir / "source.dfy").write_text(dafny_code)

    prompt = f"""Translate this Dafny program to Verus (Rust verification tool).

Translate the FORMAL SPECIFICATION ONLY (task.dfy). We will add proofs/assertions later.

RULES:
1. `ghost predicate` → `spec fn name(...) -> bool`
2. `ghost function` returning int → `spec fn name(...) -> int`
3. `method` → `fn name(...)` with `requires` and `ensures` clauses
4. Use `int` for spec-level integers, `Seq<int>` for sequences in spec context
5. For executable method parameters: use `&Vec<i64>` for `seq<int>`, `i64` for `int`
6. Use `a@` to get the spec view of a `Vec<i64>` (gives `Seq<i64>`), then `.map_values(|x: i64| x as int)` if you need `Seq<int>`
7. Translate `forall i | 0 <= i < |s| :: P(i)` → `forall|i: int| 0 <= i < s.len() ==> P(i)`
8. Translate `exists i | 0 <= i < |s| :: P(i)` → `exists|i: int| 0 <= i < s.len() && P(i)`
9. Dafny `|s|` → `s.len()` (spec) or `s.len()` (exec)
10. Dafny `s[i]` → `s[i]` (spec with int index) or `s[i as usize]` (exec)
11. Dafny `s[..n]` → `s.take(n)` (spec on Seq) or `s.subrange(0, n)`
12. Dafny `s + [x]` → `s.push(x)` (spec on Seq, returns new Seq)
13. Dafny `s + t` → `s.add(t)` or `s + t` (spec on Seq)
14. Method body: translate the algorithm faithfully. Use `let mut` for mutable vars.
15. For loops: add `#[verifier::loop_isolation(false)]` on the enclosing function.
    Do NOT add loop invariants (we add those later). Just add a `decreases` if needed.
16. For `assert` statements: translate to `proof {{ assume(false); }}` as placeholder (we add real proofs later).
17. Wrap everything in `verus! {{ }}` macro.
18. Add `use vstd::prelude::*;` at the top.
19. Add `fn main() {{}}` at the end.
20. Make sure it compiles with `verus --no-verify`.

Dafny source ({problem}):
```dafny
{dafny_code}
```

Output ONLY the Rust/Verus code. No explanations. Start with `use vstd::prelude::*;`"""

    for attempt in range(max_attempts):
        print(f"  [{problem}] Attempt {attempt + 1}...")

        # Call claude CLI
        try:
            r = subprocess.run(
                ["claude", "-p", prompt, "--model", "sonnet"],
                capture_output=True, text=True, timeout=180
            )
            response = r.stdout.strip()
        except (subprocess.TimeoutExpired, FileNotFoundError) as e:
            return {"status": "error", "error": str(e)}

        # Extract code from response
        code = extract_code(response)
        if not code:
            print(f"  [{problem}] No code extracted, retrying...")
            continue

        # Save the attempt
        (out_dir / f"attempt_{attempt}.rs").write_text(code)

        # Try to compile with verus (just type-check, not verify)
        ok, output = check_verus(code, out_dir)
        if ok:
            (out_dir / "translated.rs").write_text(code)
            return {
                "status": "translated",
                "attempts": attempt + 1,
                "lines_dafny": line_count,
                "lines_verus": len(code.splitlines()),
            }

        # If compilation failed, ask for a fix
        error_msg = extract_errors(output)
        print(f"  [{problem}] Compile error, fixing...")
        prompt = f"""This Verus translation has errors when compiled with `verus --no-verify`. Fix them.

Errors:
{error_msg[:1500]}

Current code:
```rust
{code}
```

Original Dafny:
```dafny
{dafny_code}
```

Remember: use `spec fn` for ghost predicates/functions, `fn` for methods, `int`/`Seq<int>` in spec mode, `i64`/`Vec<i64>` in exec mode, `a@.map_values(|x: i64| x as int)` to convert. Wrap in `verus! {{ }}`. Make it compile with `verus --no-verify`.

Output ONLY the fixed Rust/Verus code. No explanations. Start with `use vstd::prelude::*;`"""

    return {
        "status": "failed",
        "attempts": max_attempts,
        "lines_dafny": line_count,
        "last_error": error_msg[:500] if 'error_msg' in dir() else "unknown",
    }


def extract_code(response: str) -> str | None:
    """Extract Rust code from LLM response."""
    import re
    # Try ```rust blocks
    for pattern in [r'```rust\s*(.*?)\s*```', r'```\s*(.*?)\s*```']:
        m = re.search(pattern, response, re.DOTALL)
        if m:
            return m.group(1).strip()
    # If response contains "use vstd" anywhere, extract from there
    if "use vstd" in response:
        idx = response.index("use vstd")
        return response[idx:].strip()
    # If response contains "verus!" anywhere
    if "verus!" in response:
        idx = response.index("verus!")
        # Try to find a "use vstd" before it
        prefix = response[:idx]
        use_idx = prefix.rfind("use ")
        if use_idx >= 0:
            return response[use_idx:].strip()
        return response[idx:].strip()
    return None


def check_verus(code: str, out_dir: Path) -> tuple[bool, str]:
    """Check if Verus code compiles (type-checks). Not full verification."""
    rs_path = out_dir / "check.rs"
    rs_path.write_text(code)
    try:
        r = subprocess.run(
            [VERUS_BIN, str(rs_path), "--no-verify"],
            capture_output=True, text=True, timeout=60
        )
        output = r.stdout + "\n" + r.stderr
        # Verus with --no-verify succeeds if no compilation errors
        ok = r.returncode == 0
        return ok, output
    except (subprocess.TimeoutExpired, FileNotFoundError) as e:
        return False, str(e)


def extract_errors(output: str) -> str:
    """Extract error lines from Verus output."""
    lines = output.split("\n")
    errors = [l for l in lines if "error" in l.lower() and not l.strip().startswith("//")]
    return "\n".join(errors[:10]) if errors else output[:500]


def main():
    parser = argparse.ArgumentParser(description="Translate Dafny to Verus")
    parser.add_argument("--problems", nargs="+", help="Specific problems to translate")
    parser.add_argument("--max-lines", type=int, default=None, help="Max lines in task.dfy")
    parser.add_argument("--limit", type=int, default=None, help="Max problems to translate")
    parser.add_argument("--max-attempts", type=int, default=3, help="Max attempts per problem")
    args = parser.parse_args()

    OUTPUT_DIR.mkdir(parents=True, exist_ok=True)

    status = load_status()

    if args.problems:
        problems = args.problems
    else:
        # Get all verified problems, sorted by line count (shortest first)
        all_problems = get_verified_problems()
        problems_with_lines = [(p, get_line_count(p)) for p in all_problems]
        problems_with_lines.sort(key=lambda x: x[1])

        if args.max_lines:
            problems_with_lines = [(p, n) for p, n in problems_with_lines if n <= args.max_lines]

        problems = [p for p, _ in problems_with_lines]

    # Skip already translated/failed
    todo = [p for p in problems if p not in status["translated"] and p not in status.get("skipped", {})]
    if args.limit:
        todo = todo[:args.limit]

    print(f"Verus translation: {len(todo)} problems to translate")
    print(f"  Already translated: {len(status['translated'])}")
    print(f"  Already failed: {len(status['failed'])}")
    print()

    for i, problem in enumerate(todo):
        lines = get_line_count(problem)
        print(f"[{i+1}/{len(todo)}] {problem} ({lines} lines)")

        result = translate_one(problem, max_attempts=args.max_attempts)
        status_key = result["status"]

        if status_key == "translated":
            status["translated"][problem] = result
            print(f"  TRANSLATED ({result['attempts']} attempts, {result['lines_verus']} Verus lines)")
        elif status_key == "failed":
            status["failed"][problem] = result
            print(f"  FAILED ({result['attempts']} attempts)")
        else:
            status["failed"][problem] = result
            print(f"  ERROR: {result.get('error', 'unknown')}")

        save_status(status)

    # Print summary
    print(f"\n{'='*60}")
    print(f"TRANSLATION SUMMARY")
    print(f"{'='*60}")
    print(f"Translated: {len(status['translated'])}")
    print(f"Failed:     {len(status['failed'])}")
    print(f"Skipped:    {len(status.get('skipped', {}))}")
    total = len(get_verified_problems())
    print(f"Remaining:  {total - len(status['translated']) - len(status['failed']) - len(status.get('skipped', {}))}")


if __name__ == "__main__":
    main()

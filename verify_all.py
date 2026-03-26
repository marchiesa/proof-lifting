#!/usr/bin/env python3
"""
Verify all Dafny problems in the dataset.

Convenience wrapper around quirk_finder.py --verify-only.

Usage:
    python3 verify_all.py                          # All problems, 10 workers
    python3 verify_all.py --workers 5              # 5 parallel workers
    python3 verify_all.py --problems 0 1 2         # Specific problems by index
    python3 verify_all.py --names 0000_1013_A      # Specific problems by name
    python3 verify_all.py --skip-verified           # Skip already-verified problems
    python3 verify_all.py --timeout 600             # 10 min per problem (default: 15 min)

Can also be run directly via:
    python3 smt_analysis/quirk_finder.py --all --verify-only --workers 10
"""

import argparse
import json
import subprocess
import sys
import time
from concurrent.futures import ProcessPoolExecutor, as_completed
from pathlib import Path

PROJ_ROOT = Path(__file__).parent.resolve()
DATASET_DIR = PROJ_ROOT / "dataset"
DOTNET = "/opt/homebrew/Cellar/dotnet@8/8.0.124/libexec/dotnet"
DAFNY_DLL = PROJ_ROOT / "dafny-source" / "Binaries" / "Dafny.dll"


def get_problem_dirs() -> list[Path]:
    """List all problem directories that have a task.dfy."""
    dirs = sorted(DATASET_DIR.iterdir())
    return [d for d in dirs if d.is_dir() and (d / "task.dfy").exists()]


def is_already_verified(problem_dir: Path) -> bool:
    """Check if a problem already has a verified.dfy that passes dafny verify."""
    verified = problem_dir / "verified.dfy"
    return verified.exists()


def quick_verify(dfy_file: Path, timeout: int = 60) -> tuple[bool, str]:
    """Run dafny verify and return (success, output)."""
    try:
        result = subprocess.run(
            [DOTNET, str(DAFNY_DLL), "verify", str(dfy_file),
             "--verification-time-limit", str(timeout)],
            capture_output=True, text=True, timeout=timeout + 30,
        )
        output = result.stdout + result.stderr
        success = "0 errors" in output and "Error" not in output.split("0 errors")[0].split("\n")[-1]
        return success, output
    except subprocess.TimeoutExpired:
        return False, "TIMEOUT"
    except Exception as e:
        return False, f"EXCEPTION: {e}"


def build_verify_prompt(problem_dir: Path) -> str:
    """Build the prompt for Claude Code to verify a problem."""
    task = (problem_dir / "task.dfy").read_text()
    problem_name = problem_dir.name

    # Include problem description if available
    problem_desc = ""
    problem_json = problem_dir / "problem.json"
    if problem_json.exists():
        try:
            p = json.loads(problem_json.read_text())
            problem_desc = f"\n## Problem: {p.get('title', problem_name)}\n{p.get('description', '')}\n"
        except json.JSONDecodeError:
            pass

    return f"""Make this Dafny program verify. Add loop invariants, assertions, ghost variables,
and/or lemmas as needed. Do NOT modify the ghost spec (functions, predicates) or the method
signature (requires, ensures). Only add proof annotations inside method bodies.
{problem_desc}
## File: {problem_dir}/task.dfy

```dafny
{task}
```

## Instructions:

1. Read the code carefully. Understand what the method does and what the spec requires.

2. Add loop invariants for every loop. Common patterns:
   - Bounds: `invariant 0 <= i <= |s|`
   - Accumulator: `invariant acc == F(s[..i])` for recursive ghost functions
   - Sequence slicing: `assert s[..i+1] == s[..i] + [s[i]];` before using F(s[..i+1])
   - Full slice identity: `assert s[..|s|] == s;` after loops that process entire sequences
   - Type preservation: `invariant AllNonNeg(s[..i])` if needed by the spec

3. Add helper lemmas if needed. For example:
   - `lemma SumAppend(s: seq<int>, v: int) ensures Sum(s + [v]) == Sum(s) + v`
   - Lemma calls inside loop bodies to connect the invariant to the next iteration

4. Run dafny verify:
   ```bash
   {DOTNET} {DAFNY_DLL} verify {problem_dir}/verified.dfy --verification-time-limit 60
   ```

5. If verification fails, read the error, fix the code, and retry. Common issues:
   - "invariant could not be proved to be maintained" → missing assertion before the update
   - "postcondition could not be proved" → missing assertion or lemma call after the loop
   - "decreases expression might not decrease" → add explicit decreases clause

6. Write the final result to `{problem_dir}/verified.dfy`.
   Also write `{problem_dir}/verify_result.json` with:
   ```json
   {{
     "verified": true/false,
     "attempts": N,
     "error": "last error if failed, null if verified"
   }}
   ```

7. If you cannot verify it after several attempts, still save your best attempt as
   `verified.dfy` and set `"verified": false` in the result JSON. Include the error.

IMPORTANT: Write the verified file to {problem_dir}/verified.dfy (not task.dfy).
Do NOT modify task.dfy.
"""


def verify_problem(problem_dir: Path, timeout: int = 900) -> dict:
    """Run Claude Code to verify a single problem."""
    name = problem_dir.name
    t0 = time.time()

    prompt = build_verify_prompt(problem_dir)

    try:
        result = subprocess.run(
            [
                "claude", "-p",
                "--dangerously-skip-permissions",
                "--no-session-persistence",
                "--verbose",
                "--max-turns", "40",
            ],
            input=prompt,
            capture_output=True,
            text=True,
            timeout=timeout,
            cwd=str(problem_dir),
        )
        elapsed = time.time() - t0

        # Check if verified.dfy was produced and verifies
        verified_file = problem_dir / "verified.dfy"
        verified = False
        if verified_file.exists():
            ok, output = quick_verify(verified_file)
            verified = ok

        # Check if Claude wrote a result JSON
        result_file = problem_dir / "verify_result.json"
        if result_file.exists():
            try:
                rj = json.loads(result_file.read_text())
                if not verified and rj.get("verified"):
                    # Claude thinks it verified but our check says no — trust our check
                    rj["verified"] = False
                    result_file.write_text(json.dumps(rj, indent=2))
            except json.JSONDecodeError:
                pass

        status = {
            "problem": name,
            "verified": verified,
            "time_seconds": round(elapsed, 1),
            "exit_code": result.returncode,
        }

        tag = "VERIFIED" if verified else "FAILED"
        print(f"[{name}] {tag} in {elapsed:.0f}s")
        return status

    except subprocess.TimeoutExpired:
        elapsed = time.time() - t0
        print(f"[{name}] TIMEOUT after {elapsed:.0f}s")
        return {
            "problem": name,
            "verified": False,
            "time_seconds": round(elapsed, 1),
            "exit_code": -1,
            "error": "timeout",
        }
    except Exception as e:
        elapsed = time.time() - t0
        print(f"[{name}] ERROR: {e}")
        return {
            "problem": name,
            "verified": False,
            "time_seconds": round(elapsed, 1),
            "exit_code": -1,
            "error": str(e),
        }


def main():
    parser = argparse.ArgumentParser(description="Verify all Dafny problems in the dataset")
    parser.add_argument("--workers", type=int, default=10,
                        help="Number of parallel Claude Code instances (default: 10)")
    parser.add_argument("--timeout", type=int, default=900,
                        help="Timeout per problem in seconds (default: 900 = 15 min)")
    parser.add_argument("--problems", type=int, nargs="+",
                        help="Problem indices to verify (0-based)")
    parser.add_argument("--names", type=str, nargs="+",
                        help="Problem names to verify (e.g., 0000_1013_A)")
    parser.add_argument("--skip-verified", action="store_true",
                        help="Skip problems that already have verified.dfy")
    args = parser.parse_args()

    all_dirs = get_problem_dirs()

    # Filter by index
    if args.problems is not None:
        dirs = [all_dirs[i] for i in args.problems if i < len(all_dirs)]
    elif args.names is not None:
        name_set = set(args.names)
        dirs = [d for d in all_dirs if d.name in name_set]
    else:
        dirs = all_dirs

    # Skip already verified
    if args.skip_verified:
        before = len(dirs)
        dirs = [d for d in dirs if not is_already_verified(d)]
        skipped = before - len(dirs)
        if skipped > 0:
            print(f"Skipping {skipped} already-verified problems")

    if not dirs:
        print("No problems to verify.")
        return

    print(f"Verifying {len(dirs)} problems with {args.workers} workers, {args.timeout}s timeout")
    print()

    results = []
    t0 = time.time()

    if args.workers == 1:
        for d in dirs:
            r = verify_problem(d, args.timeout)
            results.append(r)
    else:
        with ProcessPoolExecutor(max_workers=args.workers) as executor:
            futures = {executor.submit(verify_problem, d, args.timeout): d.name for d in dirs}
            for future in as_completed(futures):
                r = future.result()
                results.append(r)
                verified_count = sum(1 for x in results if x["verified"])
                total = len(results)
                print(f"  Progress: {total}/{len(dirs)} "
                      f"({verified_count} verified, {total - verified_count} failed)")

    elapsed = time.time() - t0

    # Summary
    verified_count = sum(1 for r in results if r["verified"])
    failed = [r for r in results if not r["verified"]]

    print()
    print("=" * 60)
    print(f"RESULTS: {verified_count}/{len(results)} verified")
    print(f"Total time: {elapsed:.0f}s ({elapsed/60:.1f} min)")
    print("=" * 60)

    if failed:
        print(f"\nFailed problems ({len(failed)}):")
        for r in sorted(failed, key=lambda x: x["problem"]):
            err = r.get("error", "verification failed")
            print(f"  {r['problem']}: {err}")

    # Save summary
    summary = {
        "total": len(results),
        "verified": verified_count,
        "failed": len(failed),
        "total_time_seconds": round(elapsed, 1),
        "results": sorted(results, key=lambda x: x["problem"]),
    }
    summary_file = DATASET_DIR / "verify_summary.json"
    summary_file.write_text(json.dumps(summary, indent=2))
    print(f"\nSummary written to: {summary_file}")


if __name__ == "__main__":
    main()

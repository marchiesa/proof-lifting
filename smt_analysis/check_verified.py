#!/usr/bin/env python3
"""Check which verified.dfy files actually verify with the current (fixed) Boogie.

Writes two output files:
  smt_analysis/results/verification_status.json  — full results per problem
  smt_analysis/results/verified_problems.txt     — list of problem IDs that pass

Usage:
    python3 smt_analysis/check_verified.py
"""

import json
import subprocess
import sys
import time
from pathlib import Path

PROJ_ROOT = Path(__file__).parent.parent.resolve()
RESULTS_DIR = PROJ_ROOT / "smt_analysis" / "results"
ABLATION_SH = PROJ_ROOT / "smt_analysis" / "helpers" / "run_ablation.sh"


def check_one(dfy_path: Path, timeout: int = 60) -> dict:
    """Run dafny verify on a file. Return {result, errors, time}."""
    try:
        proc = subprocess.run(
            ["bash", str(ABLATION_SH), str(dfy_path), str(timeout)],
            capture_output=True, text=True, timeout=timeout + 60,
        )
        try:
            data = json.loads(proc.stdout)
        except json.JSONDecodeError:
            data = {"result": "parse_error", "raw_output": proc.stdout[:500]}
    except subprocess.TimeoutExpired:
        data = {"result": "timeout"}
    return data


def main():
    problem_dirs = sorted(
        d for d in RESULTS_DIR.iterdir()
        if d.is_dir() and (d / "verified.dfy").exists()
    )

    print(f"Checking {len(problem_dirs)} verified.dfy files...")

    results = {}
    pass_count = 0
    fail_count = 0

    for i, pdir in enumerate(problem_dirs):
        dfy = pdir / "verified.dfy"
        t0 = time.time()
        data = check_one(dfy)
        elapsed = time.time() - t0

        status = data["result"]
        errors = [e for e in data.get("errors", []) if "Model parsing" not in e]

        results[pdir.name] = {
            "status": status,
            "time": round(elapsed, 2),
            "errors": errors[:3],
        }

        if status == "pass":
            pass_count += 1
            print(f"[{i+1:3d}/{len(problem_dirs)}] {pdir.name}: PASS ({elapsed:.1f}s)")
        else:
            fail_count += 1
            print(f"[{i+1:3d}/{len(problem_dirs)}] {pdir.name}: FAIL ({status}, {elapsed:.1f}s)")
            for e in errors[:2]:
                print(f"    {e}")

    # Write full results
    status_file = RESULTS_DIR / "verification_status.json"
    status_file.write_text(json.dumps({
        "total": len(problem_dirs),
        "pass": pass_count,
        "fail": fail_count,
        "per_problem": results,
    }, indent=2))
    print(f"\nFull results written to: {status_file}")

    # Write list of passing problems
    passing = sorted(name for name, r in results.items() if r["status"] == "pass")
    problems_file = RESULTS_DIR / "verified_problems.txt"
    problems_file.write_text("\n".join(passing) + "\n")
    print(f"Passing problems ({len(passing)}) written to: {problems_file}")

    # Summary
    print(f"\n=== SUMMARY ===")
    print(f"Total: {len(problem_dirs)}")
    print(f"Pass:  {pass_count}")
    print(f"Fail:  {fail_count}")


if __name__ == "__main__":
    main()

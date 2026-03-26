#!/usr/bin/env python3
"""
Repair script: re-run step 4b + 4c for problems that have a working task.dfy
but whose tests.dfy doesn't test the top-level ensures predicate.

Reads existing task.dfy, working_impl.dfy, io_pairs.json, negative_pairs.json, problem.json.
Only regenerates the testable spec and test file.
"""

import json
import sys
import time
import shutil
from pathlib import Path
from concurrent.futures import ProcessPoolExecutor, as_completed
from pipeline import (
    step4b_testable_spec, step4c_spec_tests, step4_fix,
    run_dafny, call_claude, extract_dafny_block,
)

DATASET_DIR = Path("dataset")
TIMEOUT_SECONDS = 3600

# The 15 problems with specs but missing top-level predicate tests
PROBLEMS_TO_FIX = [
    "0037_1150_A",
]


def repair_problem(problem_name):
    """Re-run 4b + 4c for one problem."""
    problem_dir = DATASET_DIR / problem_name
    start_time = time.time()

    print(f"\n{'='*60}")
    print(f"Repairing: {problem_name}")
    print(f"{'='*60}")

    # Load existing files
    task_dfy = (problem_dir / "task.dfy").read_text()
    working_impl = (problem_dir / "working_impl.dfy").read_text()
    with open(problem_dir / "problem.json") as f:
        problem = json.load(f)
    with open(problem_dir / "io_pairs.json") as f:
        io_pairs = json.load(f)
    with open(problem_dir / "negative_pairs.json") as f:
        negative_pairs = json.load(f)

    def timed_out():
        if time.time() - start_time > TIMEOUT_SECONDS:
            print(f"  TIMEOUT after {time.time() - start_time:.0f}s")
            return True
        return False

    def retry_step_local(step_fn, step_name, *args, **kwargs):
        attempt = 0
        while not timed_out():
            attempt += 1
            result = step_fn(*args, **kwargs)
            if result:
                return result
            print(f"  {step_name}: attempt {attempt} failed, retrying...")
        return None

    # Step 4b: testable spec
    print("  Step 4b: Getting testable spec...")
    testable_spec = retry_step_local(step4b_testable_spec, "step4b", problem, task_dfy)
    if not testable_spec:
        print("  FAILED: No testable spec")
        return False

    # Step 4c: spec + impl tests
    print("  Step 4c: Getting spec + impl tests...")
    spec_tests = retry_step_local(step4c_spec_tests, "step4c", testable_spec, io_pairs, negative_pairs, problem)
    if not spec_tests:
        print("  FAILED: No spec tests")
        return False

    tests_content = spec_tests
    (problem_dir / "tests.dfy").write_text(tests_content)

    # Test — retry with fixes until passing or timeout
    while not timed_out():
        print(f"  Testing spec...")
        success, output = run_dafny(problem_dir / "tests.dfy")

        if success and "All tests passed" in output:
            print(f"  Spec works!")
            break

        print(f"  Failed. Fixing...")
        fixed = retry_step_local(step4_fix, "step4_fix", tests_content, output)
        if fixed:
            tests_content = fixed
            (problem_dir / "tests.dfy").write_text(tests_content)
        else:
            print(f"  FAILED: Could not fix spec tests")
            return False
    else:
        return False

    # Clean up build artifacts
    keep = {"problem.json", "solution.py", "io_pairs.json", "negative_pairs.json",
            "signature.txt", "task.dfy", "tests.dfy", "working_impl.dfy"}
    for f in problem_dir.iterdir():
        if f.name in keep:
            continue
        if f.is_dir():
            shutil.rmtree(f)
        else:
            f.unlink()

    elapsed = time.time() - start_time
    print(f"  SUCCESS in {elapsed:.0f}s")
    return True


def _worker(problem_name):
    try:
        ok = repair_problem(problem_name)
    except Exception as e:
        print(f"  [{problem_name}] EXCEPTION: {e}")
        ok = False
    return problem_name, ok


def main():
    import argparse
    parser = argparse.ArgumentParser()
    parser.add_argument("--workers", type=int, default=5)
    args = parser.parse_args()

    problems = PROBLEMS_TO_FIX
    print(f"Repairing {len(problems)} problems with {args.workers} workers")

    # Log file
    log_path = DATASET_DIR / "repair_log.txt"

    success_count = 0
    fail_count = 0

    if args.workers <= 1:
        for name in problems:
            _, ok = _worker(name)
            if ok:
                success_count += 1
            else:
                fail_count += 1
    else:
        with ProcessPoolExecutor(max_workers=args.workers) as executor:
            futures = {executor.submit(_worker, name): name for name in problems}
            for future in as_completed(futures):
                name, ok = future.result()
                if ok:
                    success_count += 1
                else:
                    fail_count += 1
                print(f"  Progress: {success_count + fail_count}/{len(problems)} done ({success_count} ok, {fail_count} failed)")

    summary = f"\nDone: {success_count} success, {fail_count} failed out of {len(problems)}"
    print(summary)

    with open(log_path, "w") as f:
        f.write(f"Repair run at {time.strftime('%Y-%m-%d %H:%M:%S')}\n")
        f.write(summary + "\n\n")
        for name in problems:
            tests_path = DATASET_DIR / name / "tests.dfy"
            f.write(f"{'='*60}\n")
            f.write(f"{name}\n")
            f.write(f"{'='*60}\n")
            if tests_path.exists():
                f.write(tests_path.read_text())
            else:
                f.write("(no tests.dfy)\n")
            f.write("\n\n")
    print(f"All tests logged to {log_path}")


if __name__ == "__main__":
    main()

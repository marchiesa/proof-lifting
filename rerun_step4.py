#!/usr/bin/env python3
"""Re-run only step 4 (formal spec) on problems that already have working implementations.

Uses the new pipeline flow:
  4a: Generate testable spec (compilable, bounded, slicing)
  4c: Generate tests, validate against I/O pairs
  4b: Derive ghost spec from tested testable spec (minimal diff)
"""

import json
import sys
import time
import shutil
from pathlib import Path
from concurrent.futures import ProcessPoolExecutor, as_completed

from pipeline import (
    step4a_testable_spec, step4b_ghost_spec, step4c_spec_tests,
    step4_diagnose_negative, step4_fix, step4_fix_spec,
    generate_negative_outputs, run_dafny,
    DATASET_DIR,
)

TIMEOUT_SECONDS = 1800  # 30 min per problem (step 4 only)


def rerun_step4(problem_dir):
    """Re-run step 4 on a single problem directory."""
    start_time = time.time()
    name = problem_dir.name

    # Load existing data
    problem = json.loads((problem_dir / "problem.json").read_text())
    working_impl = (problem_dir / "working_impl.dfy").read_text()
    io_pairs = json.loads((problem_dir / "io_pairs.json").read_text())

    # Regenerate negative pairs (in case format changed)
    negative_pairs = generate_negative_outputs(io_pairs)

    def timed_out():
        return time.time() - start_time > TIMEOUT_SECONDS

    def retry(fn, label, *args, **kwargs):
        attempt = 0
        while not timed_out():
            attempt += 1
            result = fn(*args, **kwargs)
            if result:
                return result
            print(f"  [{name}] {label}: attempt {attempt} failed, retrying...")
        return None

    # ── STEP 4a: Testable spec ──
    print(f"  [{name}] Step 4a: Testable spec...")
    testable_spec = retry(step4a_testable_spec, "step4a", problem, working_impl)
    if not testable_spec:
        print(f"  [{name}] FAILED: No testable spec")
        return False

    # ── STEP 4c: Spec tests ──
    print(f"  [{name}] Step 4c: Spec tests...")
    spec_tests = retry(step4c_spec_tests, "step4c", testable_spec, io_pairs, negative_pairs, problem)
    if not spec_tests:
        print(f"  [{name}] FAILED: No spec tests")
        return False

    tests_content = spec_tests
    with open(problem_dir / "tests.dfy", "w") as f:
        f.write(tests_content)

    # Test spec — retry with fixes
    while not timed_out():
        print(f"  [{name}] Testing spec...")
        success, output = run_dafny(problem_dir / "tests.dfy")

        if success and "All tests passed" in output:
            print(f"  [{name}] Spec works!")
            break

        # Diagnose negative test failures
        if "spec should reject" in output and "expectation violation" in output.lower():
            for neg in negative_pairs:
                verdict, fix = step4_diagnose_negative(
                    testable_spec, neg["input"], neg["output"],
                    neg["original_output"], problem
                )
                if verdict == "alternative":
                    print(f"  [{name}] Valid alternative, removing negative test")
                    negative_pairs = [n for n in negative_pairs if n != neg]
                elif verdict == "spec_bug":
                    print(f"  [{name}] Spec bug, fixing...")
                    fixed_spec = step4_fix_spec(testable_spec, problem, fix, neg)
                    if fixed_spec:
                        testable_spec = fixed_spec
                    break

            spec_tests = retry(step4c_spec_tests, "step4c_regen", testable_spec, io_pairs, negative_pairs, problem)
            if spec_tests:
                tests_content = spec_tests
                with open(problem_dir / "tests.dfy", "w") as f:
                    f.write(tests_content)
            continue

        print(f"  [{name}] Failed. Fixing...")
        fixed = retry(step4_fix, "step4_fix", tests_content, output)
        if fixed:
            tests_content = fixed
            with open(problem_dir / "tests.dfy", "w") as f:
                f.write(tests_content)
        else:
            print(f"  [{name}] FAILED: Could not fix spec")
            return False
    else:
        print(f"  [{name}] TIMEOUT")
        return False

    # ── STEP 4b: Ghost spec ──
    print(f"  [{name}] Step 4b: Ghost spec...")
    ghost_spec = retry(step4b_ghost_spec, "step4b", problem, testable_spec)
    if not ghost_spec:
        print(f"  [{name}] FAILED: No ghost spec")
        return False

    with open(problem_dir / "task.dfy", "w") as f:
        f.write(ghost_spec)

    # Save negative pairs
    with open(problem_dir / "negative_pairs.json", "w") as f:
        json.dump(negative_pairs, f, indent=2)

    elapsed = time.time() - start_time
    print(f"  [{name}] SUCCESS in {elapsed:.0f}s")
    return True


def worker(problem_dir_str):
    problem_dir = Path(problem_dir_str)
    try:
        ok = rerun_step4(problem_dir)
    except Exception as e:
        print(f"  [{problem_dir.name}] EXCEPTION: {e}")
        ok = False
    return problem_dir.name, ok


def main():
    import argparse
    parser = argparse.ArgumentParser()
    parser.add_argument("--workers", type=int, default=10)
    parser.add_argument("--indices", type=str, default=None,
                        help="Comma-separated indices to rerun, e.g. '0,1,5'")
    args = parser.parse_args()

    # Find all problem dirs with working_impl.dfy
    dirs = sorted(DATASET_DIR.iterdir())
    dirs = [d for d in dirs if d.is_dir() and (d / "working_impl.dfy").exists()]

    if args.indices:
        indices = set(int(x) for x in args.indices.split(","))
        dirs = [d for d in dirs if int(d.name.split("_")[0]) in indices]

    print(f"Re-running step 4 on {len(dirs)} problems with {args.workers} workers")

    success = 0
    fail = 0

    with ProcessPoolExecutor(max_workers=args.workers) as pool:
        futures = {pool.submit(worker, str(d)): d.name for d in dirs}
        for future in as_completed(futures):
            name, ok = future.result()
            if ok:
                success += 1
            else:
                fail += 1
            print(f"  Progress: {success + fail}/{len(dirs)} ({success} ok, {fail} failed)")

    print(f"\nDone: {success} success, {fail} failed")


if __name__ == "__main__":
    main()

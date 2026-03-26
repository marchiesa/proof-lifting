#!/usr/bin/env python3
"""Re-run step 4 ONLY on problems whose task.dfy doesn't contain slicing (..).

If the new version still doesn't have slicing, restore the old version.
If the new version has slicing, keep it.
"""

import json
import sys
import time
import shutil
from pathlib import Path
from concurrent.futures import ProcessPoolExecutor, as_completed

from rerun_step4 import rerun_step4
from pipeline import DATASET_DIR


def has_slicing(dfy_path: Path) -> bool:
    """Check if a .dfy file contains sequence slicing (..)."""
    text = dfy_path.read_text()
    return ".." in text


def worker(problem_dir_str):
    problem_dir = Path(problem_dir_str)
    name = problem_dir.name
    task_path = problem_dir / "task.dfy"
    tests_path = problem_dir / "tests.dfy"

    # Backup old versions
    old_task = task_path.read_text()
    old_tests = tests_path.read_text() if tests_path.exists() else None

    try:
        ok = rerun_step4(problem_dir)
    except Exception as e:
        print(f"  [{name}] EXCEPTION: {e}")
        ok = False

    if ok and has_slicing(task_path):
        print(f"  [{name}] NEW SPEC HAS SLICING - keeping new version")
        return name, "improved"
    elif ok:
        # New spec succeeded but still no slicing — restore old version
        print(f"  [{name}] New spec has no slicing - restoring old version")
        task_path.write_text(old_task)
        if old_tests is not None:
            tests_path.write_text(old_tests)
        return name, "no_change"
    else:
        # Failed — restore old version
        print(f"  [{name}] FAILED - restoring old version")
        task_path.write_text(old_task)
        if old_tests is not None:
            tests_path.write_text(old_tests)
        return name, "failed"


def main():
    import argparse
    parser = argparse.ArgumentParser()
    parser.add_argument("--workers", type=int, default=5)
    args = parser.parse_args()

    # Find problems WITHOUT slicing
    dirs = sorted(DATASET_DIR.iterdir())
    dirs = [d for d in dirs if d.is_dir()
            and (d / "task.dfy").exists()
            and not has_slicing(d / "task.dfy")]

    print(f"Found {len(dirs)} problems without slicing")
    print(f"Running step 4 with {args.workers} workers")
    print()

    results = {"improved": [], "no_change": [], "failed": []}

    with ProcessPoolExecutor(max_workers=args.workers) as pool:
        futures = {pool.submit(worker, str(d)): d.name for d in dirs}
        for future in as_completed(futures):
            name, status = future.result()
            results[status].append(name)
            total = sum(len(v) for v in results.values())
            print(f"  Progress: {total}/{len(dirs)} "
                  f"({len(results['improved'])} improved, "
                  f"{len(results['no_change'])} unchanged, "
                  f"{len(results['failed'])} failed)")

    print(f"\nDone:")
    print(f"  Improved (now has slicing): {len(results['improved'])}")
    for name in sorted(results['improved']):
        print(f"    {name}")
    print(f"  No change (still no slicing): {len(results['no_change'])}")
    print(f"  Failed: {len(results['failed'])}")


if __name__ == "__main__":
    main()

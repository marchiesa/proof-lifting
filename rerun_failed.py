#!/usr/bin/env python3
"""Re-run pipeline on specific failed problem indices."""

import time
from pathlib import Path
from concurrent.futures import ProcessPoolExecutor, as_completed
from pipeline import load_data, process_problem, _process_worker, DATASET_DIR, QUEUE_DIR

# The 20 problems that need reprocessing (19 queue + 0041 partial)
INDICES = [10, 17, 21, 25, 35, 41, 50, 52, 55, 67, 69, 82, 86, 87, 89, 90, 94, 97, 98, 99]
WORKERS = 5

def main():
    DATASET_DIR.mkdir(exist_ok=True)
    QUEUE_DIR.mkdir(exist_ok=True)

    data = load_data()
    data = [p for p in data if p["rating"] <= 1600]
    data.sort(key=lambda p: p["rating"])

    work_items = [(data[idx], idx) for idx in INDICES]
    print(f"Re-running {len(work_items)} problems with {WORKERS} workers")

    success_count = 0
    fail_count = 0

    import shutil
    with ProcessPoolExecutor(max_workers=WORKERS) as executor:
        futures = {executor.submit(_process_worker, item): item for item in work_items}
        for future in as_completed(futures):
            idx, pid, ok = future.result()
            problem_dir = DATASET_DIR / f"{idx:04d}_{pid}"
            if ok:
                success_count += 1
            else:
                fail_count += 1
                queue_dest = QUEUE_DIR / f"{idx:04d}_{pid}"
                if problem_dir.exists():
                    if queue_dest.exists():
                        shutil.rmtree(queue_dest)
                    shutil.move(str(problem_dir), str(queue_dest))
            print(f"  Progress: {success_count + fail_count}/{len(work_items)} done ({success_count} ok, {fail_count} failed)")

    print(f"\nDone: {success_count} success, {fail_count} failed")

if __name__ == "__main__":
    main()

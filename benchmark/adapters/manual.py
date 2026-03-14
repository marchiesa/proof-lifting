"""
Manual adapter for the Dafny benchmark.

Prints instructions and waits for the user to solve the task interactively.
Useful for human baselines or debugging.
"""

import os
import time

from .base_adapter import BaseAdapter, Result


class ManualAdapter(BaseAdapter):
    """
    Adapter that prints the task to the user and waits for them to
    solve it manually.
    """

    def __init__(self):
        super().__init__(name="manual")

    def run(
        self,
        problem_dir: str,
        working_dir: str,
        timeout: int,
        max_iterations: int,
        env: dict,
    ) -> Result:
        task_file = os.path.join(working_dir, "task.dfy")
        log_file = env.get("BENCHMARK_LOG_FILE", "/tmp/benchmark.log")

        print("\n" + "=" * 60)
        print("MANUAL BENCHMARK MODE")
        print("=" * 60)
        print(f"\nTask file: {task_file}")
        print(f"Original:  {env.get('BENCHMARK_TASK_FILE', 'unknown')}")
        print(f"Log file:  {log_file}")
        print(f"Timeout:   {timeout}s")
        print(f"Max iterations: {max_iterations}")
        print()

        # Read and display the file
        with open(task_file, 'r') as f:
            content = f.read()
        print("--- File contents ---")
        print(content)
        print("--- End file contents ---")
        print()
        print("Instructions:")
        print("  1. Edit the file at the path above")
        print("  2. Run: dafny verify " + task_file)
        print("     (The proxy dafny on PATH will be used)")
        print("  3. When done, press Enter here")
        print()

        # Set up environment display
        print("Environment variables set:")
        for key in sorted(env.keys()):
            if key.startswith("BENCHMARK_"):
                print(f"  {key}={env[key]}")
        print()

        start_time = time.time()

        try:
            input("Press Enter when finished (or Ctrl+C to abort)...")
        except KeyboardInterrupt:
            elapsed = time.time() - start_time
            return Result(
                success=False,
                iterations=self._read_iteration_count(log_file),
                time_seconds=elapsed,
                solution_path=task_file,
                error="User aborted",
                log_path=log_file,
            )

        elapsed = time.time() - start_time
        iterations = self._read_iteration_count(log_file)
        success = self._check_success(log_file)

        return Result(
            success=success,
            iterations=iterations,
            time_seconds=elapsed,
            solution_path=task_file,
            log_path=log_file,
        )

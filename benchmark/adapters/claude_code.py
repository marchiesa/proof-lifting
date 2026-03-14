"""
Claude Code adapter for the Dafny benchmark.

Launches the `claude` CLI with a prompt to solve a Dafny verification task.
"""

import os
import subprocess
import time
import json
from typing import Optional

from .base_adapter import BaseAdapter, Result


class ClaudeCodeAdapter(BaseAdapter):
    """
    Adapter that runs Claude Code (the `claude` CLI) on a Dafny task.
    """

    def __init__(self, model: str = ""):
        super().__init__(name="claude-code")
        self.model = model

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

        # Read problem description if available
        desc_file = os.path.join(problem_dir, "description.txt")
        description = ""
        if os.path.exists(desc_file):
            with open(desc_file, 'r') as f:
                description = f.read().strip()

        prompt = self.get_task_prompt(task_file, description)

        # Build the claude command
        cmd = ["claude", "--print", "--verbose"]
        if self.model:
            cmd.extend(["--model", self.model])

        # Add max turns — each "turn" can include a dafny verify call
        # We set this high and rely on the proxy's iteration tracking
        cmd.extend(["--max-turns", str(max_iterations * 2)])

        # Add the prompt
        cmd.extend(["--prompt", prompt])

        # Set up environment
        run_env = os.environ.copy()
        run_env.update(env)

        start_time = time.time()
        timed_out = False
        raw_output = ""

        try:
            result = subprocess.run(
                cmd,
                cwd=working_dir,
                env=run_env,
                timeout=timeout,
                capture_output=True,
                text=True,
            )
            raw_output = result.stdout + "\n" + result.stderr
        except subprocess.TimeoutExpired as e:
            timed_out = True
            raw_output = (e.stdout or b"").decode() + "\n" + (e.stderr or b"").decode()
        except Exception as e:
            elapsed = time.time() - start_time
            return Result(
                success=False,
                iterations=self._read_iteration_count(log_file),
                time_seconds=elapsed,
                solution_path=task_file if os.path.exists(task_file) else None,
                error=str(e),
                log_path=log_file,
                raw_output="",
            )

        elapsed = time.time() - start_time
        iterations = self._read_iteration_count(log_file)
        success = self._check_success(log_file)

        # Also check if the final file verifies by looking at output
        if not success and not timed_out:
            # Check if "0 errors" appears in the raw output
            if "0 errors" in raw_output:
                success = True

        return Result(
            success=success,
            iterations=iterations,
            time_seconds=elapsed,
            solution_path=task_file if os.path.exists(task_file) else None,
            timed_out=timed_out,
            max_iterations_reached=(iterations >= max_iterations),
            log_path=log_file,
            raw_output=raw_output,
        )

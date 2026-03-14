"""
Base adapter for LLM benchmark runners.

Each adapter implements a `run()` method that launches an LLM to solve a
Dafny verification task. The LLM is given the task file and can call
`dafny verify` (which is intercepted by the proxy).
"""

from abc import ABC, abstractmethod
from dataclasses import dataclass, field
from typing import Optional
import time


@dataclass
class Result:
    """Result of a single benchmark run on a single problem."""
    success: bool
    iterations: int
    time_seconds: float
    solution_path: Optional[str]
    error: Optional[str] = None
    timed_out: bool = False
    max_iterations_reached: bool = False
    log_path: Optional[str] = None
    raw_output: Optional[str] = None

    def to_dict(self) -> dict:
        return {
            'success': self.success,
            'iterations': self.iterations,
            'time_seconds': round(self.time_seconds, 2),
            'solution_path': self.solution_path,
            'error': self.error,
            'timed_out': self.timed_out,
            'max_iterations_reached': self.max_iterations_reached,
            'log_path': self.log_path,
        }


class BaseAdapter(ABC):
    """
    Abstract base class for LLM adapters.

    Subclasses must implement `run()`, which launches an LLM on a Dafny
    verification task.
    """

    def __init__(self, name: str):
        self.name = name

    @abstractmethod
    def run(
        self,
        problem_dir: str,
        working_dir: str,
        timeout: int,
        max_iterations: int,
        env: dict,
    ) -> Result:
        """
        Run the LLM on a Dafny verification task.

        Args:
            problem_dir: Directory containing the original task.dfy
            working_dir: Temporary working directory with a copy of task.dfy
            timeout: Maximum time in seconds
            max_iterations: Maximum number of dafny verify calls
            env: Environment variables dict (includes BENCHMARK_* vars)

        Returns:
            Result object with success/failure details
        """
        pass

    def get_task_prompt(self, task_path: str, problem_description: str = "") -> str:
        """
        Generate the prompt to send to the LLM.

        Args:
            task_path: Path to the .dfy file the LLM should work on
            problem_description: Optional human-readable description

        Returns:
            Prompt string
        """
        desc = ""
        if problem_description:
            desc = f"\n\nProblem description: {problem_description}\n"

        return f"""Add loop invariants and proof annotations to make this Dafny program verify successfully.
{desc}
Rules:
- Do NOT modify the code logic, method signatures, or formal specification (predicates, functions, datatypes).
- You may ONLY add: loop invariants, assertions, lemmas, ghost variables, decreases clauses, and calc blocks.
- The file is at: {task_path}
- Use `dafny verify {task_path}` to check your work.
- Keep trying until verification succeeds or you are confident it cannot be done.
- If verification fails, read the error messages carefully and adjust your annotations.

Start by reading the file, understanding what it does, and then add the necessary proof annotations."""

    def _read_iteration_count(self, log_file: str) -> int:
        """Read the current iteration count from the proxy's iteration file."""
        iteration_file = f"{log_file}.iteration"
        try:
            with open(iteration_file, 'r') as f:
                return int(f.read().strip())
        except (FileNotFoundError, ValueError):
            return 0

    def _check_success(self, log_file: str) -> bool:
        """Check if the last verification attempt succeeded by reading the log."""
        try:
            with open(log_file, 'r') as f:
                content = f.read()
            # Find the last RESULT line
            results = [line for line in content.splitlines()
                       if line.startswith('RESULT:')]
            if results:
                return results[-1] == 'RESULT: VERIFICATION_SUCCESS'
        except FileNotFoundError:
            pass
        return False

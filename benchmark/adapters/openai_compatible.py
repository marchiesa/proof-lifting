"""
OpenAI-compatible API adapter for the Dafny benchmark.

Works with any server exposing the /v1/chat/completions endpoint,
including vLLM, TGI, Ollama, and OpenAI itself.

Uses only the `requests` library (no openai SDK dependency).
"""

import json
import os
import re
import time
from typing import Optional

import requests

from .base_adapter import BaseAdapter, Result


# System prompt explaining the Dafny verification task and expected output format.
SYSTEM_PROMPT = """\
You are an expert Dafny verification engineer. Your task is to add proof \
annotations to a Dafny program so that it verifies successfully.

Rules:
- Do NOT modify the code logic, method signatures, or formal specification \
(predicates, functions, datatypes).
- You may ONLY add: loop invariants, assertions, lemmas, ghost variables, \
decreases clauses, calc blocks, and forall proof statements.
- When you provide a modified file, wrap the ENTIRE file contents in a fenced \
code block marked ```dafny ... ```.
- If verification fails, read the error messages carefully and adjust your \
annotations. Keep trying until it succeeds.
"""


def _extract_dfy_code(text: str) -> Optional[str]:
    """
    Extract the contents of the first ```dafny ... ``` fenced block.

    Falls back to the first generic ``` ... ``` block if no dafny-tagged
    block is found.  Returns None if no code block is present.
    """
    # Try dafny-tagged block first
    m = re.search(r"```dafny\s*\n(.*?)```", text, re.DOTALL)
    if m:
        return m.group(1).strip()
    # Fall back to any fenced block
    m = re.search(r"```\s*\n(.*?)```", text, re.DOTALL)
    if m:
        return m.group(1).strip()
    return None


class OpenAICompatibleAdapter(BaseAdapter):
    """
    Adapter that calls an OpenAI-compatible chat completions API.

    Parameters
    ----------
    base_url : str
        Base URL for the API, e.g. ``http://localhost:8000/v1``.
    model_name : str
        Model identifier passed in the API request body.
    api_key : str, optional
        Bearer token.  Defaults to the ``OPENAI_API_KEY`` env var, then
        to the literal string ``"none"`` (sufficient for local servers).
    temperature : float
        Sampling temperature.
    max_tokens : int
        Maximum tokens per completion.
    top_p : float
        Nucleus sampling parameter.
    """

    def __init__(
        self,
        base_url: str = "http://localhost:8000/v1",
        model_name: str = "default",
        api_key: Optional[str] = None,
        temperature: float = 0.6,
        max_tokens: int = 4096,
        top_p: float = 0.95,
    ):
        super().__init__(name="openai_compatible")
        self.base_url = base_url.rstrip("/")
        self.model_name = model_name
        self.api_key = api_key or os.environ.get("OPENAI_API_KEY", "none")
        self.temperature = temperature
        self.max_tokens = max_tokens
        self.top_p = top_p

    # ------------------------------------------------------------------
    # Internal helpers
    # ------------------------------------------------------------------

    def _completions_url(self) -> str:
        return f"{self.base_url}/chat/completions"

    def _headers(self) -> dict:
        return {
            "Content-Type": "application/json",
            "Authorization": f"Bearer {self.api_key}",
        }

    def _call_api(self, messages: list, retries: int = 3) -> str:
        """
        Send a chat-completion request and return the assistant message text.

        Retries up to *retries* times on transient HTTP / connection errors.
        """
        payload = {
            "model": self.model_name,
            "messages": messages,
            "temperature": self.temperature,
            "max_tokens": self.max_tokens,
            "top_p": self.top_p,
        }
        last_error: Optional[Exception] = None
        for attempt in range(1, retries + 1):
            try:
                resp = requests.post(
                    self._completions_url(),
                    headers=self._headers(),
                    json=payload,
                    timeout=300,
                )
                resp.raise_for_status()
                data = resp.json()
                return data["choices"][0]["message"]["content"]
            except (requests.RequestException, KeyError, json.JSONDecodeError) as exc:
                last_error = exc
                if attempt < retries:
                    wait = 2 ** attempt
                    time.sleep(wait)
        raise RuntimeError(
            f"API call failed after {retries} attempts: {last_error}"
        )

    # ------------------------------------------------------------------
    # BaseAdapter interface
    # ------------------------------------------------------------------

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

        # Read problem description if available.
        desc_file = os.path.join(problem_dir, "description.txt")
        description = ""
        if os.path.exists(desc_file):
            with open(desc_file, "r") as fh:
                description = fh.read().strip()

        # Read the initial task source.
        with open(task_file, "r") as fh:
            current_source = fh.read()

        # Build the initial conversation.
        messages: list = [
            {"role": "system", "content": SYSTEM_PROMPT},
            {
                "role": "user",
                "content": self._make_initial_prompt(current_source, description),
            },
        ]

        start_time = time.time()
        timed_out = False
        error_msg: Optional[str] = None
        iterations = 0

        for iteration in range(1, max_iterations + 1):
            # Check wall-clock timeout.
            if time.time() - start_time >= timeout:
                timed_out = True
                break

            # Ask the model for a modified file.
            try:
                assistant_reply = self._call_api(messages)
            except RuntimeError as exc:
                error_msg = str(exc)
                break

            messages.append({"role": "assistant", "content": assistant_reply})

            # Extract code from the response.
            new_code = _extract_dfy_code(assistant_reply)
            if new_code is None:
                # Model did not produce a code block; ask it to try again.
                messages.append(
                    {
                        "role": "user",
                        "content": (
                            "I could not find a ```dafny code block in your "
                            "response. Please provide the complete modified "
                            "file inside a ```dafny ... ``` block."
                        ),
                    }
                )
                continue

            # Write the candidate solution.
            with open(task_file, "w") as fh:
                fh.write(new_code + "\n")

            # Run dafny verify via the proxy (respects BENCHMARK_* env).
            import subprocess

            run_env = os.environ.copy()
            run_env.update(env)
            try:
                proc = subprocess.run(
                    ["dafny", "verify", task_file],
                    cwd=working_dir,
                    env=run_env,
                    capture_output=True,
                    text=True,
                    timeout=min(120, max(timeout - int(time.time() - start_time), 10)),
                )
                verify_output = proc.stdout + "\n" + proc.stderr
            except subprocess.TimeoutExpired:
                verify_output = "dafny verify timed out"
            except FileNotFoundError:
                verify_output = "ERROR: dafny binary not found on PATH"

            iterations = self._read_iteration_count(log_file)

            # Check success.
            if self._check_success(log_file):
                elapsed = time.time() - start_time
                return Result(
                    success=True,
                    iterations=iterations,
                    time_seconds=elapsed,
                    solution_path=task_file,
                    log_path=log_file,
                )

            # Feed errors back to the model.
            messages.append(
                {
                    "role": "user",
                    "content": (
                        f"Verification failed (attempt {iteration}/{max_iterations}).\n\n"
                        f"Dafny output:\n```\n{verify_output}\n```\n\n"
                        "Please fix the annotations and provide the complete "
                        "file again inside a ```dafny ... ``` block."
                    ),
                }
            )

        elapsed = time.time() - start_time
        iterations = self._read_iteration_count(log_file)
        return Result(
            success=False,
            iterations=iterations,
            time_seconds=elapsed,
            solution_path=task_file if os.path.exists(task_file) else None,
            timed_out=timed_out,
            max_iterations_reached=(iterations >= max_iterations),
            error=error_msg,
            log_path=log_file,
        )

    # ------------------------------------------------------------------
    # Prompt construction
    # ------------------------------------------------------------------

    @staticmethod
    def _make_initial_prompt(source: str, description: str) -> str:
        parts = ["Here is the Dafny file that needs proof annotations:\n"]
        if description:
            parts.append(f"Problem description: {description}\n")
        parts.append(f"```dafny\n{source}\n```\n")
        parts.append(
            "Add the necessary loop invariants and proof annotations so "
            "that `dafny verify` succeeds. Return the complete modified "
            "file inside a ```dafny ... ``` block."
        )
        return "\n".join(parts)

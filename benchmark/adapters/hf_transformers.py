"""
HuggingFace Transformers adapter for the Dafny benchmark.

Runs inference directly on a local GPU using ``transformers`` and ``torch``.
All heavy imports are deferred so that the benchmark can be imported and used
with other adapters even when torch is not installed.

Supports tensor-parallel multi-GPU via ``torch.distributed`` when the model is
loaded with ``device_map="auto"`` (the default for large models).
"""

import os
import re
import subprocess
import time
from typing import Optional

from .base_adapter import BaseAdapter, Result


# Re-use the same system prompt as the OpenAI-compatible adapter.
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
    """Extract the first ```dafny ... ``` (or plain ```) code block."""
    m = re.search(r"```dafny\s*\n(.*?)```", text, re.DOTALL)
    if m:
        return m.group(1).strip()
    m = re.search(r"```\s*\n(.*?)```", text, re.DOTALL)
    if m:
        return m.group(1).strip()
    return None


class HFTransformersAdapter(BaseAdapter):
    """
    Adapter that performs local inference with a HuggingFace causal-LM.

    Parameters
    ----------
    model_path : str
        HuggingFace model ID or local path (e.g. ``meta-llama/Llama-3.1-8B-Instruct``).
    device : str
        PyTorch device string.  ``"auto"`` uses ``device_map="auto"`` for
        multi-GPU tensor parallelism.  ``"cuda:0"`` pins to a single GPU.
    dtype : str
        Data type: ``"float16"``, ``"bfloat16"``, or ``"auto"``.
    max_new_tokens : int
        Maximum tokens to generate per turn.
    temperature : float
        Sampling temperature.
    top_p : float
        Nucleus sampling parameter.
    """

    def __init__(
        self,
        model_path: str = "meta-llama/Llama-3.1-8B-Instruct",
        device: str = "auto",
        dtype: str = "bfloat16",
        max_new_tokens: int = 4096,
        temperature: float = 0.6,
        top_p: float = 0.95,
    ):
        super().__init__(name="hf_transformers")
        self.model_path = model_path
        self.device = device
        self.dtype = dtype
        self.max_new_tokens = max_new_tokens
        self.temperature = temperature
        self.top_p = top_p

        # Lazily initialised in _ensure_model_loaded().
        self._model = None
        self._tokenizer = None

    # ------------------------------------------------------------------
    # Lazy model loading
    # ------------------------------------------------------------------

    def _ensure_model_loaded(self) -> None:
        """Load the model and tokenizer on first use."""
        if self._model is not None:
            return

        # Deferred imports so the module can be imported without torch.
        import torch
        from transformers import AutoModelForCausalLM, AutoTokenizer

        dtype_map = {
            "float16": torch.float16,
            "bfloat16": torch.bfloat16,
            "float32": torch.float32,
            "auto": "auto",
        }
        torch_dtype = dtype_map.get(self.dtype, "auto")

        print(f"  [hf_transformers] Loading model: {self.model_path}")
        print(f"  [hf_transformers] device={self.device}  dtype={self.dtype}")

        load_kwargs: dict = {
            "torch_dtype": torch_dtype,
            "trust_remote_code": True,
        }
        if self.device == "auto":
            load_kwargs["device_map"] = "auto"

        self._tokenizer = AutoTokenizer.from_pretrained(
            self.model_path, trust_remote_code=True
        )
        self._model = AutoModelForCausalLM.from_pretrained(
            self.model_path, **load_kwargs
        )

        if self.device != "auto":
            self._model = self._model.to(self.device)

        # Make sure pad_token is set.
        if self._tokenizer.pad_token is None:
            self._tokenizer.pad_token = self._tokenizer.eos_token

        self._model.eval()
        print("  [hf_transformers] Model loaded.")

    # ------------------------------------------------------------------
    # Generation
    # ------------------------------------------------------------------

    def _generate(self, messages: list) -> str:
        """
        Generate a completion from the chat *messages* list.

        Uses the tokenizer's ``apply_chat_template`` when available.
        """
        import torch

        self._ensure_model_loaded()
        assert self._tokenizer is not None
        assert self._model is not None

        # Build prompt via chat template (works for Llama-3, Mistral, etc.)
        if hasattr(self._tokenizer, "apply_chat_template"):
            prompt_ids = self._tokenizer.apply_chat_template(
                messages,
                add_generation_prompt=True,
                return_tensors="pt",
            )
        else:
            # Fallback: concatenate role/content pairs.
            text = ""
            for m in messages:
                text += f"<|{m['role']}|>\n{m['content']}\n"
            text += "<|assistant|>\n"
            prompt_ids = self._tokenizer.encode(text, return_tensors="pt")

        device = next(self._model.parameters()).device
        prompt_ids = prompt_ids.to(device)

        with torch.no_grad():
            output_ids = self._model.generate(
                prompt_ids,
                max_new_tokens=self.max_new_tokens,
                temperature=self.temperature if self.temperature > 0 else None,
                top_p=self.top_p if self.temperature > 0 else None,
                do_sample=self.temperature > 0,
                pad_token_id=self._tokenizer.pad_token_id,
            )

        # Decode only the newly-generated tokens.
        new_tokens = output_ids[0][prompt_ids.shape[-1]:]
        return self._tokenizer.decode(new_tokens, skip_special_tokens=True)

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

        # Build conversation.
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

        # Load model (may be slow on first call; cached thereafter).
        try:
            self._ensure_model_loaded()
        except Exception as exc:
            return Result(
                success=False,
                iterations=0,
                time_seconds=time.time() - start_time,
                solution_path=task_file,
                error=f"Failed to load model: {exc}",
                log_path=log_file,
            )

        for iteration in range(1, max_iterations + 1):
            if time.time() - start_time >= timeout:
                timed_out = True
                break

            try:
                assistant_reply = self._generate(messages)
            except Exception as exc:
                error_msg = f"Generation error: {exc}"
                break

            messages.append({"role": "assistant", "content": assistant_reply})

            new_code = _extract_dfy_code(assistant_reply)
            if new_code is None:
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

            with open(task_file, "w") as fh:
                fh.write(new_code + "\n")

            # Run dafny verify via the proxy.
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

            if self._check_success(log_file):
                return Result(
                    success=True,
                    iterations=iterations,
                    time_seconds=time.time() - start_time,
                    solution_path=task_file,
                    log_path=log_file,
                )

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

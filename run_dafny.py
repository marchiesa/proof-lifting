from __future__ import annotations

import asyncio
import dataclasses
import os
import time
from pathlib import Path


PROJ_ROOT = Path(__file__).resolve().parent
DAFNY_DLL = PROJ_ROOT / "dafny-source" / "Binaries" / "Dafny.dll"


@dataclasses.dataclass
class DafnyArgs:
    file_path: Path
    verification_time_limit: int = 60
    prelude_file: Path | None = None
    isolate_assertions: bool = False
    extra_args: list[str] = dataclasses.field(default_factory=list)
    cwd: Path | None = None
    timeout_seconds: int | None = None


@dataclasses.dataclass
class DafnyOutput:
    command: list[str]
    return_code: int
    stdout: str
    stderr: str
    elapsed_seconds: float
    timed_out: bool
    result: str
    errors: list[str]
    raw_output: str


@dataclasses.dataclass
class CustomDafnyArgs(DafnyArgs):
    ast_mapping_file: Path | None = None
    bprint_file: Path | None = None
    no_verify: bool = False
    compile_target: str | None = None


@dataclasses.dataclass
class CustomDafnyOutput(DafnyOutput):
    ast_mapping_file: str | None = None
    bprint_file: str | None = None


def _dotnet() -> str:
    return os.environ.get("DOTNET8", os.environ.get("DOTNET", "dotnet"))


def _classify_output(raw_output: str) -> tuple[str, list[str]]:
    lower = raw_output.lower()
    if "timed out" in lower or "time out" in lower:
        result = "timeout"
    elif "parse error" in lower or "not expected in dafny" in lower:
        result = "parse_error"
    elif "model parsing error" in lower or "could not parse any models" in lower:
        result = "prover_error"
    elif "0 errors" in raw_output:
        result = "pass"
    else:
        result = "error"

    errors: list[str] = []
    for line in raw_output.splitlines():
        stripped = line.strip()
        if not stripped:
            continue
        if "verified, 0 errors" in stripped:
            continue
        if "error" in stripped.lower() or "could not be proved" in stripped.lower():
            errors.append(stripped)
            if len(errors) >= 5:
                break
    return result, errors


def _build_verify_command(args: DafnyArgs) -> list[str]:
    command = [_dotnet(), str(DAFNY_DLL), "verify", str(args.file_path)]
    if args.prelude_file is not None:
        command.extend(["--prelude", str(args.prelude_file)])
    if args.isolate_assertions:
        command.append("--isolate-assertions")
    command.extend(["--verification-time-limit", str(args.verification_time_limit)])
    command.extend(args.extra_args)
    return command


def _build_custom_command(args: CustomDafnyArgs) -> list[str]:
    subcommand = "run" if args.no_verify else "verify"
    command = [_dotnet(), str(DAFNY_DLL), subcommand, str(args.file_path)]
    if args.no_verify:
        command.append("--no-verify")
    if args.prelude_file is not None:
        command.extend(["--prelude", str(args.prelude_file)])
    if args.isolate_assertions:
        command.append("--isolate-assertions")
    if args.ast_mapping_file is not None:
        command.extend(["--ast-mapping", str(args.ast_mapping_file)])
    if args.bprint_file is not None:
        command.extend(["--bprint", str(args.bprint_file)])
    if args.compile_target is not None:
        command.extend(["--target", args.compile_target])
    command.extend(["--verification-time-limit", str(args.verification_time_limit)])
    command.extend(args.extra_args)
    return command


async def _run_command(
    command: list[str],
    cwd: Path | None = None,
    timeout_seconds: int | None = None,
) -> tuple[int, str, str, float, bool]:
    start = time.time()
    proc = await asyncio.create_subprocess_exec(
        *command,
        cwd=str(cwd) if cwd is not None else None,
        stdout=asyncio.subprocess.PIPE,
        stderr=asyncio.subprocess.PIPE,
    )
    timed_out = False
    try:
        stdout_b, stderr_b = await asyncio.wait_for(
            proc.communicate(),
            timeout=timeout_seconds,
        )
    except asyncio.TimeoutError:
        timed_out = True
        proc.kill()
        stdout_b, stderr_b = await proc.communicate()
    elapsed = round(time.time() - start, 2)
    stdout = stdout_b.decode()
    stderr = stderr_b.decode()
    if timed_out:
        return_code = -1
        stderr = (stderr + "\nTIMED OUT").strip()
    else:
        return_code = proc.returncode
    return return_code, stdout, stderr, elapsed, timed_out


async def _run_dafny(args: DafnyArgs) -> DafnyOutput:
    command = _build_verify_command(args)
    timeout = args.timeout_seconds or (args.verification_time_limit + 30)
    return_code, stdout, stderr, elapsed, timed_out = await _run_command(
        command,
        cwd=args.cwd,
        timeout_seconds=timeout,
    )
    raw_output = (stdout or "") + (stderr or "")
    result, errors = _classify_output(
        raw_output if not timed_out else raw_output + "\nTIMED OUT"
    )
    if timed_out:
        result = "timeout"
    return DafnyOutput(
        command=command,
        return_code=return_code,
        stdout=stdout,
        stderr=stderr,
        elapsed_seconds=elapsed,
        timed_out=timed_out,
        result=result,
        errors=errors,
        raw_output=raw_output,
    )


async def _run_custom_dafny(args: CustomDafnyArgs) -> CustomDafnyOutput:
    command = _build_custom_command(args)
    timeout = args.timeout_seconds or (args.verification_time_limit + 30)
    return_code, stdout, stderr, elapsed, timed_out = await _run_command(
        command,
        cwd=args.cwd,
        timeout_seconds=timeout,
    )
    raw_output = (stdout or "") + (stderr or "")
    result, errors = _classify_output(
        raw_output if not timed_out else raw_output + "\nTIMED OUT"
    )
    if timed_out:
        result = "timeout"
    return CustomDafnyOutput(
        command=command,
        return_code=return_code,
        stdout=stdout,
        stderr=stderr,
        elapsed_seconds=elapsed,
        timed_out=timed_out,
        result=result,
        errors=errors,
        raw_output=raw_output,
        ast_mapping_file=str(args.ast_mapping_file) if args.ast_mapping_file else None,
        bprint_file=str(args.bprint_file) if args.bprint_file else None,
    )


@dataclasses.dataclass
class DafnyPool:
    max_concurrency: int = 1

    def __post_init__(self):
        self._semaphore = asyncio.Semaphore(self.max_concurrency)

    async def run_dafny(self, args: DafnyArgs) -> DafnyOutput:
        async with self._semaphore:
            return await _run_dafny(args)

    async def run_custom_dafny(self, args: CustomDafnyArgs) -> CustomDafnyOutput:
        async with self._semaphore:
            return await _run_custom_dafny(args)

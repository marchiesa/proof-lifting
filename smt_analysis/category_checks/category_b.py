#!/usr/bin/env python3
"""Detect Category B assertions using alternative Dafny preludes.

Given a Dafny file where one essential assertion has already been removed,
this module reruns verification with an extended prelude. If the full
extended prelude makes the file verify, it then reruns with each isolated
prelude to determine which axiom category or categories suffice.
"""

from __future__ import annotations

import argparse
import asyncio
import json
import sys
from dataclasses import asdict, dataclass
from pathlib import Path


PROJ_ROOT = Path(__file__).resolve().parents[2]
if str(PROJ_ROOT) not in sys.path:
    sys.path.insert(0, str(PROJ_ROOT))

from run_dafny import DafnyArgs, DafnyOutput, DafnyPool  # noqa: E402

DEFAULT_PRELUDE = PROJ_ROOT / "dafny-source" / "Binaries" / "DafnyPrelude.bpl"
PRELUDE_DIR = PROJ_ROOT / "ExtendedPreludes"


@dataclass(frozen=True)
class PreludeSpec:
    name: str
    prelude_path: Path
    description: str


@dataclass
class PreludeRunResult(DafnyOutput):
    name: str
    description: str
    prelude: str


@dataclass
class CategoryBResult:
    dfy_file: str
    assertion_line: int
    assertion_text: str
    timeout_seconds: int
    category_b: bool
    baseline: PreludeRunResult
    full_prelude: PreludeRunResult
    isolated_preludes: list[PreludeRunResult]
    sufficient_isolated_preludes: list[str]


FULL_PRELUDE = PreludeSpec(
    name="full",
    prelude_path=PRELUDE_DIR / "full.bpl",
    description="All additional sequence axioms",
)

ISOLATED_PRELUDES = [
    PreludeSpec(
        name="taketake",
        prelude_path=PRELUDE_DIR / "taketake.bpl",
        description="Take-of-take axiom",
    ),
    PreludeSpec(
        name="takeappend",
        prelude_path=PRELUDE_DIR / "takeappend.bpl",
        description="Take-of-append axiom",
    ),
    PreludeSpec(
        name="takefull",
        prelude_path=PRELUDE_DIR / "takefull.bpl",
        description="Take-of-full-length axiom",
    ),
    PreludeSpec(
        name="appendempty",
        prelude_path=PRELUDE_DIR / "appendempty.bpl",
        description="Append-empty identity axioms",
    ),
]


async def _verify_with_prelude(
    pool: DafnyPool,
    dfy_file: Path,
    prelude: Path,
    timeout: int,
    *,
    name: str,
    description: str,
) -> PreludeRunResult:
    output = await pool.run_dafny(
        DafnyArgs(
            file_path=dfy_file,
            prelude_file=prelude,
            verification_time_limit=timeout,
            timeout_seconds=timeout + 30,
        )
    )
    return PreludeRunResult(
        command=output.command,
        return_code=output.return_code,
        stdout=output.stdout,
        stderr=output.stderr,
        elapsed_seconds=output.elapsed_seconds,
        timed_out=output.timed_out,
        result=output.result,
        errors=output.errors,
        raw_output=output.raw_output,
        name=name,
        description=description,
        prelude=str(prelude),
    )


def _read_assertion_line(dfy_file: Path, line_number: int) -> str:
    lines = dfy_file.read_text().splitlines()
    if line_number < 1 or line_number > len(lines):
        raise ValueError(
            f"Line {line_number} is out of range for {dfy_file} "
            f"(file has {len(lines)} lines)"
        )
    return lines[line_number - 1].strip()


async def categorize_assertion_with_preludes_async(
    pool: DafnyPool,
    dfy_file: str | Path,
    assertion_line: int,
    timeout: int = 60,
) -> CategoryBResult:
    path = Path(dfy_file).resolve()
    if not path.exists():
        raise FileNotFoundError(path)

    assertion_text = _read_assertion_line(path, assertion_line)

    baseline = await _verify_with_prelude(
        pool,
        path,
        DEFAULT_PRELUDE,
        timeout,
        name="default",
        description="Default Dafny prelude",
    )
    full_run = await _verify_with_prelude(
        pool,
        path,
        FULL_PRELUDE.prelude_path,
        timeout,
        name=FULL_PRELUDE.name,
        description=FULL_PRELUDE.description,
    )

    isolated_runs: list[PreludeRunResult] = []
    sufficient_preludes: list[str] = []
    if full_run.result == "pass":
        for spec in ISOLATED_PRELUDES:
            run = await _verify_with_prelude(
                pool,
                path,
                spec.prelude_path,
                timeout,
                name=spec.name,
                description=spec.description,
            )
            isolated_runs.append(run)
            if run.result == "pass":
                sufficient_preludes.append(spec.name)

    return CategoryBResult(
        dfy_file=str(path),
        assertion_line=assertion_line,
        assertion_text=assertion_text,
        timeout_seconds=timeout,
        category_b=full_run.result == "pass",
        baseline=baseline,
        full_prelude=full_run,
        isolated_preludes=isolated_runs,
        sufficient_isolated_preludes=sufficient_preludes,
    )


def categorize_assertion_with_preludes(
    dfy_file: str | Path,
    assertion_line: int,
    timeout: int = 60,
    max_concurrency: int = 1,
) -> CategoryBResult:
    """Classify one assertion-removal variant against the extended preludes."""
    pool = DafnyPool(max_concurrency=max_concurrency)
    return asyncio.run(
        categorize_assertion_with_preludes_async(
            pool=pool,
            dfy_file=dfy_file,
            assertion_line=assertion_line,
            timeout=timeout,
        )
    )


def _build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(
        description="Detect Category B by rerunning Dafny with alternative preludes."
    )
    parser.add_argument("dfy_file", help="Path to the .dfy file to verify")
    parser.add_argument(
        "--line",
        type=int,
        required=True,
        help="1-based line number containing the relevant assertion",
    )
    parser.add_argument(
        "--timeout",
        type=int,
        default=60,
        help="Verification time limit in seconds",
    )
    parser.add_argument(
        "--max-concurrency",
        type=int,
        default=1,
        help="Maximum number of Dafny subprocesses to run concurrently",
    )
    return parser


def main() -> int:
    args = _build_parser().parse_args()
    result = categorize_assertion_with_preludes(
        args.dfy_file,
        assertion_line=args.line,
        timeout=args.timeout,
        max_concurrency=args.max_concurrency,
    )
    print(json.dumps(asdict(result), indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

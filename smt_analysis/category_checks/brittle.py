#!/usr/bin/env python3
"""Detect brittle proofs by rerunning Dafny with different random seeds."""

from __future__ import annotations

import argparse
import asyncio
import json
import re
import sys
from dataclasses import asdict, dataclass
from pathlib import Path


PROJ_ROOT = Path(__file__).resolve().parents[2]
if str(PROJ_ROOT) not in sys.path:
    sys.path.insert(0, str(PROJ_ROOT))

from run_dafny import DafnyArgs, DafnyOutput, DafnyPool  # noqa: E402


DEFAULT_SEEDS = list(range(10))
DEFAULT_TIMEOUT_SECONDS = 1
DEFAULT_FAILURE_THRESHOLD = 1


@dataclass
class ScopeAnnotationCounts:
    name: str
    kind: str
    loc: int
    asserts: int
    invariants: int
    total_annotations: int


@dataclass
class AnnotationSummary:
    per_scope: list[ScopeAnnotationCounts]
    total_loc: int
    max_scope_loc: int
    total_annotations: int
    max_scope_annotations: int
    n_scopes: int


@dataclass
class SeedRunResult(DafnyOutput):
    seed: int


@dataclass
class BrittleProofResult:
    dfy_file: str
    timeout_seconds: int
    seeds: list[int]
    failure_threshold: int
    failed_runs: int
    brittle: bool
    pass_rate: float
    seed_results: list[SeedRunResult]
    annotation_summary: AnnotationSummary


def strip_block_comments(src: str) -> str:
    return re.sub(r"/\*.*?\*/", "", src, flags=re.DOTALL)


def extract_scopes(src: str) -> list[dict]:
    """Extract method and lemma bodies using brace matching."""
    lines = src.splitlines()
    scopes: list[dict] = []

    decl_re = re.compile(r"^\s*(method|lemma)\s+(\w+)", re.MULTILINE)
    for match in decl_re.finditer(src):
        kind = match.group(1)
        name = match.group(2)
        start_line = src[: match.start()].count("\n")

        depth = 0
        body_start = None
        for i, line in enumerate(lines[start_line:], start=start_line):
            for ch in line:
                if ch == "{":
                    if depth == 0:
                        body_start = i
                    depth += 1
                elif ch == "}":
                    depth -= 1
                    if depth == 0 and body_start is not None:
                        scopes.append(
                            {
                                "name": name,
                                "kind": kind,
                                "body_lines": lines[body_start : i + 1],
                            }
                        )
                        break
            if depth == 0 and body_start is not None:
                break

    return scopes


def compute_annotation_summary(dfy_file: str | Path) -> AnnotationSummary:
    src = strip_block_comments(Path(dfy_file).read_text())
    scopes = extract_scopes(src)

    per_scope: list[ScopeAnnotationCounts] = []
    for scope in scopes:
        body = "\n".join(scope["body_lines"])
        loc = sum(
            1
            for line in scope["body_lines"]
            if line.strip() and not line.strip().startswith("//")
        )
        asserts = len(re.findall(r"^\s*assert\b", body, re.MULTILINE))
        invariants = len(re.findall(r"^\s*invariant\b", body, re.MULTILINE))
        per_scope.append(
            ScopeAnnotationCounts(
                name=scope["name"],
                kind=scope["kind"],
                loc=loc,
                asserts=asserts,
                invariants=invariants,
                total_annotations=asserts + invariants,
            )
        )

    total_loc = sum(scope.loc for scope in per_scope)
    max_scope_loc = max((scope.loc for scope in per_scope), default=0)
    total_annotations = sum(scope.total_annotations for scope in per_scope)
    max_scope_annotations = max(
        (scope.total_annotations for scope in per_scope),
        default=0,
    )
    return AnnotationSummary(
        per_scope=per_scope,
        total_loc=total_loc,
        max_scope_loc=max_scope_loc,
        total_annotations=total_annotations,
        max_scope_annotations=max_scope_annotations,
        n_scopes=len(per_scope),
    )


async def _run_seed_once(
    pool: DafnyPool,
    dfy_file: Path,
    seed: int,
    timeout_seconds: int,
) -> SeedRunResult:
    output = await pool.run_dafny(
        DafnyArgs(
            file_path=dfy_file,
            verification_time_limit=timeout_seconds,
            timeout_seconds=timeout_seconds + 30,
            extra_args=["--boogie", f"-randomSeed:{seed}"],
        )
    )
    return SeedRunResult(
        command=output.command,
        return_code=output.return_code,
        stdout=output.stdout,
        stderr=output.stderr,
        elapsed_seconds=output.elapsed_seconds,
        timed_out=output.timed_out,
        result=output.result,
        errors=output.errors,
        raw_output=output.raw_output,
        seed=seed,
    )


async def classify_brittleness_async(
    pool: DafnyPool,
    dfy_file: str | Path,
    *,
    seeds: list[int] | None = None,
    timeout_seconds: int = DEFAULT_TIMEOUT_SECONDS,
    failure_threshold: int = DEFAULT_FAILURE_THRESHOLD,
) -> BrittleProofResult:
    path = Path(dfy_file).resolve()
    if not path.exists():
        raise FileNotFoundError(path)

    chosen_seeds = list(DEFAULT_SEEDS if seeds is None else seeds)
    seed_results = [
        await _run_seed_once(pool, path, seed, timeout_seconds)
        for seed in chosen_seeds
    ]
    failed_runs = sum(1 for result in seed_results if result.result != "pass")
    annotation_summary = compute_annotation_summary(path)

    return BrittleProofResult(
        dfy_file=str(path),
        timeout_seconds=timeout_seconds,
        seeds=chosen_seeds,
        failure_threshold=failure_threshold,
        failed_runs=failed_runs,
        brittle=failed_runs >= failure_threshold,
        pass_rate=round((len(chosen_seeds) - failed_runs) / len(chosen_seeds), 2)
        if chosen_seeds
        else 0.0,
        seed_results=seed_results,
        annotation_summary=annotation_summary,
    )


def classify_brittleness(
    dfy_file: str | Path,
    *,
    seeds: list[int] | None = None,
    timeout_seconds: int = DEFAULT_TIMEOUT_SECONDS,
    failure_threshold: int = DEFAULT_FAILURE_THRESHOLD,
    max_concurrency: int = 1,
) -> BrittleProofResult:
    pool = DafnyPool(max_concurrency=max_concurrency)
    return asyncio.run(
        classify_brittleness_async(
            pool=pool,
            dfy_file=dfy_file,
            seeds=seeds,
            timeout_seconds=timeout_seconds,
            failure_threshold=failure_threshold,
        )
    )


def _build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(
        description="Detect brittle proofs by varying Boogie random seeds."
    )
    parser.add_argument("dfy_file", help="Path to the .dfy file to verify")
    parser.add_argument(
        "--seeds",
        type=int,
        nargs="*",
        help="Explicit seed list. Defaults to 0..9",
    )
    parser.add_argument(
        "--timeout",
        type=int,
        default=DEFAULT_TIMEOUT_SECONDS,
        help="Verification time limit in seconds per seed",
    )
    parser.add_argument(
        "--failure-threshold",
        type=int,
        default=DEFAULT_FAILURE_THRESHOLD,
        help="Classify as brittle if failures >= threshold",
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
    result = classify_brittleness(
        args.dfy_file,
        seeds=args.seeds,
        timeout_seconds=args.timeout,
        failure_threshold=args.failure_threshold,
        max_concurrency=args.max_concurrency,
    )
    print(json.dumps(asdict(result), indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

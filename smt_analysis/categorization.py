#!/usr/bin/env python3
"""New categorization pipeline based on the typed categorization checks."""

from __future__ import annotations

import argparse
import asyncio
import copy
import json
import re
import sys
import tempfile
from dataclasses import asdict, dataclass, field
from pathlib import Path


PROJ_ROOT = Path(__file__).resolve().parents[1]
if str(PROJ_ROOT) not in sys.path:
    sys.path.insert(0, str(PROJ_ROOT))

from run_dafny import (  # noqa: E402
    CustomDafnyArgs,
    DafnyArgs,
    DafnyPool,
    DafnyOutput,
)
from smt_analysis.category_checks.brittle import (  # noqa: E402
    DEFAULT_FAILURE_THRESHOLD,
    DEFAULT_TIMEOUT_SECONDS,
    BrittleProofResult,
    classify_brittleness_async,
)
from smt_analysis.category_checks.category_b import (  # noqa: E402
    CategoryBResult,
    categorize_assertion_with_preludes_async,
)
from smt_analysis.category_checks.category_ematching import (  # noqa: E402
    EmatchingResult,
    classify_assertion_async,
    find_assert_expr_in_bpl,
    generate_bpl_async,
)
from smt_analysis.category_checks.category_witness import (  # noqa: E402
    WitnessResult,
    classify_witness_async,
)


RESULTS_DIR = PROJ_ROOT / "smt_analysis" / "results"


@dataclass
class EssentialAssertion:
    index: int
    line: int
    text: str
    expr: str
    is_equality: bool
    boogie_id: str
    method: str
    variant_source: str
    verification_result: str
    verification_errors: list[str]
    verification_time_seconds: float


@dataclass
class AssertionCategorization:
    assertion: EssentialAssertion
    ematching: EmatchingResult | None = None
    witness: WitnessResult | None = None
    category_b: CategoryBResult | None = None


@dataclass
class ProblemCategorization:
    problem: str
    source_file: str
    baseline_verification: DafnyOutput
    essential_assertions: list[EssentialAssertion]
    brittle: BrittleProofResult | None = None
    categorization_skipped_reason: str | None = None
    assertions: list[AssertionCategorization] = field(default_factory=list)


@dataclass
class CategorizationPipelineResult:
    problem_names: list[str]
    verification_time_limit: int
    brittle_timeout_seconds: int
    brittle_failure_threshold: int
    problems: list[ProblemCategorization]


def _is_method_in_source(dfy_path: Path, method_name: str) -> bool:
    content = dfy_path.read_text()
    return bool(re.search(rf"\bmethod\s+{re.escape(method_name)}\b", content))


def parse_assertions(source_file: Path, ast_path: Path) -> list[dict]:
    ast = json.loads(ast_path.read_text())
    assertions = []
    idx = 0
    for method in ast.get("methods", []):
        method_name = method["name"]
        if not _is_method_in_source(source_file, method_name):
            continue
        for assertion in method.get("assertions", []):
            text = assertion["text"]
            line = assertion.get("location", {}).get("line", 0)
            boogie_id = assertion.get("boogieId", "")
            is_equality = "==" in text and "!==" not in text and "<==" not in text
            if "<==>" in text:
                is_equality = True
            assertions.append(
                {
                    "index": idx,
                    "line": line,
                    "text": f"assert {text};",
                    "expr": text,
                    "is_equality": is_equality,
                    "boogie_id": boogie_id,
                    "method": method_name,
                }
            )
            idx += 1
    return assertions


def _find_assert_end(lines: list[str], start: int) -> int:
    j = start
    while j < len(lines):
        stripped = lines[j].strip()
        if "by {" in stripped or "by{" in stripped:
            depth = stripped.count("{") - stripped.count("}")
            j += 1
            while j < len(lines) and depth > 0:
                depth += lines[j].count("{") - lines[j].count("}")
                j += 1
            return j - 1
        if stripped.endswith(";"):
            k = j + 1
            while k < len(lines) and lines[k].strip() == "":
                k += 1
            if k < len(lines) and lines[k].strip().startswith("by"):
                j = k
                continue
            return j
        j += 1
    return min(j, len(lines) - 1)


def _find_statement_semicolon(line: str, start_col: int) -> int | None:
    """Find the first statement-ending semicolon after start_col.

    Ignores semicolons inside strings, chars, line comments, and block comments.
    """
    in_string = False
    in_char = False
    in_block_comment = False
    escape = False
    i = start_col

    while i < len(line):
        ch = line[i]
        nxt = line[i + 1] if i + 1 < len(line) else ""

        if in_block_comment:
            if ch == "*" and nxt == "/":
                in_block_comment = False
                i += 2
                continue
            i += 1
            continue

        if in_string:
            if escape:
                escape = False
            elif ch == "\\":
                escape = True
            elif ch == '"':
                in_string = False
            i += 1
            continue

        if in_char:
            if escape:
                escape = False
            elif ch == "\\":
                escape = True
            elif ch == "'":
                in_char = False
            i += 1
            continue

        if ch == "/" and nxt == "/":
            return None
        if ch == "/" and nxt == "*":
            in_block_comment = True
            i += 2
            continue
        if ch == '"':
            in_string = True
            i += 1
            continue
        if ch == "'":
            in_char = True
            i += 1
            continue
        if ch == ";":
            return i
        i += 1

    return None


def _find_inline_assert_span(line: str, expr: str) -> tuple[int, int] | None:
    """Find the precise span of `assert <expr>;` within one line."""
    patterns = [f"assert {expr};", f" assert {expr};"]
    for pattern in patterns:
        idx = line.find(pattern)
        if idx != -1:
            start = idx if pattern.startswith("assert") else idx + 1
            return start, start + len(pattern.lstrip())

    expr_normalized = re.sub(r"\s+", " ", expr).strip()
    prefix_match = re.search(r"assert\s+" + re.escape(expr_normalized), line)
    if not prefix_match:
        return None

    semicolon_idx = _find_statement_semicolon(line, prefix_match.start())
    if semicolon_idx is None:
        return None
    return prefix_match.start(), semicolon_idx + 1


def create_without_variant(dfy_path: Path, assertion: dict, output_path: Path) -> None:
    lines = dfy_path.read_text().split("\n")
    start = assertion["line"] - 1
    if start < 0 or start >= len(lines):
        output_path.write_text("\n".join(lines))
        return

    line = lines[start]
    stripped = line.strip()
    expr = assertion["expr"]

    inline_span = _find_inline_assert_span(line, expr)
    if inline_span is not None:
        span_start, span_end = inline_span
        lines[start] = line[:span_start] + line[span_end:]
    elif stripped.startswith("assert "):
        end = _find_assert_end(lines, start)
        for j in range(start, end + 1):
            lines[j] = "    // REMOVED: " + lines[j].strip()
    else:
        lines[start] = "    // REMOVED: " + stripped
    output_path.write_text("\n".join(lines))


def _clone_args(
    base_args: DafnyArgs, file_path: Path, extra_args: list[str] | None = None
) -> DafnyArgs:
    cloned = copy.deepcopy(base_args)
    cloned.file_path = file_path
    if extra_args is not None:
        cloned.extra_args = list(extra_args)
    return cloned


async def _generate_ast_mapping_with_args(
    pool: DafnyPool,
    dfy_path: Path,
    timeout: int,
    extra_args: list[str] | None = None,
) -> tuple[str | None, str | None, str]:
    with tempfile.TemporaryDirectory() as tmpdir:
        tmp = Path(tmpdir)
        ast_path = tmp / "ast_mapping.json"
        bpl_path = tmp / "output.bpl"
        output = await pool.run_custom_dafny(
            CustomDafnyArgs(
                file_path=dfy_path,
                verification_time_limit=timeout,
                timeout_seconds=timeout + 60,
                ast_mapping_file=ast_path,
                bprint_file=bpl_path,
                extra_args=list(extra_args or []),
            )
        )
        return (
            ast_path.read_text() if ast_path.exists() else None,
            bpl_path.read_text() if bpl_path.exists() else None,
            output.raw_output,
        )


async def _ablate_problem(
    pool: DafnyPool, problem: str, source_file: Path, base_args: DafnyArgs
) -> tuple[DafnyOutput, list[EssentialAssertion]]:
    baseline = await pool.run_dafny(_clone_args(base_args, source_file))
    if baseline.result != "pass":
        return baseline, []

    ast_text, _bpl_text, raw_output = await _generate_ast_mapping_with_args(
        pool,
        source_file,
        timeout=base_args.verification_time_limit,
        extra_args=base_args.extra_args,
    )
    if ast_text is None:
        raise RuntimeError(
            f"AST mapping not generated for {problem}: {raw_output[:500]}"
        )
    with tempfile.TemporaryDirectory(prefix=f"{problem}_ast_") as tmpdir:
        ast_path = Path(tmpdir) / "ast_mapping.json"
        ast_path.write_text(ast_text)
        assertions = parse_assertions(source_file, ast_path)

    essential: list[EssentialAssertion] = []
    with tempfile.TemporaryDirectory(prefix=f"{problem}_ablation_") as tmpdir:
        tmp = Path(tmpdir)
        for assertion in assertions:
            variant_path = tmp / f"without_{assertion['index']:02d}.dfy"
            create_without_variant(source_file, assertion, variant_path)
            variant_output = await pool.run_dafny(_clone_args(base_args, variant_path))

            if variant_output.result in {"parse_error", "prover_error"}:
                continue
            if variant_output.result == "pass":
                continue

            essential.append(
                EssentialAssertion(
                    index=assertion["index"],
                    line=assertion["line"],
                    text=assertion["text"],
                    expr=assertion["expr"],
                    is_equality=assertion["is_equality"],
                    boogie_id=assertion["boogie_id"],
                    method=assertion["method"],
                    variant_source=variant_path.read_text(),
                    verification_result=variant_output.result,
                    verification_errors=variant_output.errors,
                    verification_time_seconds=variant_output.elapsed_seconds,
                )
            )
    return baseline, essential


def _default_problem_names() -> list[str]:
    summary_path = RESULTS_DIR / "diagnosis_summary.json"
    if summary_path.exists():
        summary = json.loads(summary_path.read_text())
        return sorted(set(d["problem"] for d in summary["all_diagnoses"]))
    return sorted(
        p.name
        for p in RESULTS_DIR.iterdir()
        if p.is_dir() and (p / "verified.dfy").exists()
    )


async def _categorize_problem(
    pool: DafnyPool,
    problem: str,
    base_args: DafnyArgs,
    *,
    brittle_timeout_seconds: int,
    brittle_failure_threshold: int,
    brittle_isolate_assertions: bool,
) -> ProblemCategorization:
    problem_dir = RESULTS_DIR / problem
    source_file = problem_dir / "verified.dfy"
    baseline, essential_assertions = await _ablate_problem(
        pool, problem, source_file, base_args
    )

    result = ProblemCategorization(
        problem=problem,
        source_file=str(source_file),
        baseline_verification=baseline,
        essential_assertions=essential_assertions,
    )

    if baseline.result != "pass":
        result.categorization_skipped_reason = "baseline verification failed"
        return result

    if not essential_assertions:
        result.categorization_skipped_reason = "no essential assertions"
        return result

    brittle = await classify_brittleness_async(
        pool,
        source_file,
        timeout_seconds=brittle_timeout_seconds,
        failure_threshold=brittle_failure_threshold,
        isolate_assertions=brittle_isolate_assertions,
    )
    result.brittle = brittle
    if brittle.brittle:
        result.categorization_skipped_reason = "brittle"
        return result

    bpl_text, _ = await generate_bpl_async(
        pool, source_file, timeout=base_args.verification_time_limit
    )

    for essential in essential_assertions:
        ematching = await classify_assertion_async(
            pool,
            source_file,
            essential.boogie_id,
            timeout=base_args.verification_time_limit,
            bpl_text=bpl_text,
        )
        witness = await classify_witness_async(
            pool,
            source_file,
            essential.boogie_id,
            timeout=base_args.verification_time_limit,
            bpl_text=bpl_text,
        )
        with tempfile.TemporaryDirectory(prefix=f"{problem}_category_b_") as tmpdir:
            variant_path = Path(tmpdir) / f"without_{essential.index:02d}.dfy"
            variant_path.write_text(essential.variant_source)
            category_b = await categorize_assertion_with_preludes_async(
                pool,
                variant_path,
                assertion_line=essential.line,
                timeout=base_args.verification_time_limit,
            )
        result.assertions.append(
            AssertionCategorization(
                assertion=essential,
                ematching=ematching,
                witness=witness,
                category_b=category_b,
            )
        )

    return result


async def run_categorization_pipeline(
    base_args: DafnyArgs,
    problem_names: list[str] | None = None,
    *,
    brittle_timeout_seconds: int = DEFAULT_TIMEOUT_SECONDS,
    brittle_failure_threshold: int = DEFAULT_FAILURE_THRESHOLD,
    brittle_isolate_assertions: bool = False,
    max_dafny_concurrency: int = 1,
) -> CategorizationPipelineResult:
    names = list(problem_names or _default_problem_names())

    pool = DafnyPool(max_concurrency=max_dafny_concurrency)
    tasks = [
        _categorize_problem(
            pool,
            name,
            base_args,
            brittle_timeout_seconds=brittle_timeout_seconds,
            brittle_failure_threshold=brittle_failure_threshold,
            brittle_isolate_assertions=brittle_isolate_assertions,
        )
        for name in names
    ]
    problems = await asyncio.gather(*tasks)
    return CategorizationPipelineResult(
        problem_names=names,
        verification_time_limit=base_args.verification_time_limit,
        brittle_timeout_seconds=brittle_timeout_seconds,
        brittle_failure_threshold=brittle_failure_threshold,
        problems=problems,
    )


def _build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(
        description="Run the new categorization pipeline over verified Dafny problems."
    )
    parser.add_argument("--names", nargs="*", help="Specific problem names to process")
    parser.add_argument(
        "--verification-time-limit",
        type=int,
        default=1,
        help="Verification time limit for baseline, ablation, and A/B category tests",
    )
    parser.add_argument(
        "--prelude",
        default="",
        help="Optional alternative prelude to use for baseline verification/ablation",
    )
    parser.add_argument(
        "--isolate-assertions",
        action="store_true",
        help="Pass --isolate-assertions to Dafny during baseline/ablation verification",
    )
    parser.add_argument(
        "--brittle-failure-threshold",
        type=int,
        default=DEFAULT_FAILURE_THRESHOLD,
        help="Classify as brittle if failures >= threshold",
    )
    parser.add_argument(
        "--brittle-isolate-assertions",
        action="store_true",
        help="Pass --isolate-assertions during brittle seed-variation checks",
    )
    parser.add_argument(
        "--max-dafny-concurrency",
        type=int,
        default=1,
        help="Maximum number of Dafny subprocesses to run concurrently",
    )
    parser.add_argument(
        "--output",
        default="smt_analysis/results/new_categorization.json",
        help="Where to write the pipeline result JSON",
    )
    return parser


async def main() -> int:
    args = _build_parser().parse_args()
    base_args = DafnyArgs(
        file_path=Path("placeholder.dfy"),
        verification_time_limit=args.verification_time_limit,
        prelude_file=Path(args.prelude) if args.prelude else None,
        isolate_assertions=args.isolate_assertions,
    )
    result = await run_categorization_pipeline(
        base_args,
        problem_names=args.names,
        brittle_timeout_seconds=args.verification_time_limit,
        brittle_failure_threshold=args.brittle_failure_threshold,
        brittle_isolate_assertions=args.brittle_isolate_assertions,
        max_dafny_concurrency=args.max_dafny_concurrency,
    )
    out_path = PROJ_ROOT / args.output
    out_path.write_text(json.dumps(asdict(result), indent=2))
    print(f"Wrote {out_path}")
    return 0


if __name__ == "__main__":
    raise SystemExit(asyncio.run(main()))

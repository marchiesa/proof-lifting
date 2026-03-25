#!/usr/bin/env python3
"""
Existential witness detector for essential assertions.

For a given essential assertion (identified by boogieId), removes it from the
BPL and runs Boogie to find which VCs fail.  If any failing VC is an
existential formula, the assertion is likely providing a witness.

Two confidence levels:

  high — the assertion expression directly matches the body of a failing
         (exists x :: P(x)) via one-sided pattern matching
  low  — at least one failing VC is existential, but no direct body match
  none — no failing VCs are existential formulas

Usage:
    python3 -m smt_analysis.category_checks.category_witness \\
        --dfy smt_analysis/results/0006_1017_A/verified.dfy \\
        --boogie-id id92
"""

from __future__ import annotations

import asyncio
import json
import re
import tempfile
from dataclasses import dataclass
from pathlib import Path
from typing import Literal, Optional

from run_dafny import BoogieArgs, DafnyPool
from smt_analysis.category_checks.category_ematching import (
    Expr,
    _extract_binders,
    _parse_triggers,
    find_assert_expr_in_bpl,
    generate_bpl,
    generate_bpl_async,
    match,
    parse_expr,
    subterms,
)

WitnessConfidence = Literal["none", "low", "high"]


@dataclass
class WitnessResult:
    """
    Result of checking whether an assertion is providing an existential witness.

    confidence:
      "none" — no failing VCs are existential formulas
      "low"  — at least one failing VC is existential, but the assertion
               expression does not match any of their bodies
      "high" — assertion expression matches the body of a failing existential
               via one-sided pattern matching
    """

    boogie_id: str
    confidence: WitnessConfidence
    exists_assertions: list[str]
    matched_exists: Optional[str] = None
    note: str = ""


# ---------------------------------------------------------------------------
# BPL manipulation
# ---------------------------------------------------------------------------


def _find_assert_span(bpl_lines: list[str], boogie_id: str) -> Optional[tuple[int, int]]:
    """
    Find the start and end line indices (0-based, inclusive) of the assert
    {:id "boogie_id"} statement in the BPL.  Scans forward from the start
    line to find the terminating semicolon.
    """
    pattern = re.compile(
        r'assert\s+(?:\{[^}]*\}\s*)*\{:id\s+"' + re.escape(boogie_id) + r'"'
    )
    for i, line in enumerate(bpl_lines):
        if pattern.search(line):
            j = i
            while j < len(bpl_lines) and ";" not in bpl_lines[j]:
                j += 1
            return i, j
    return None


def _remove_assert(bpl_text: str, boogie_id: str) -> Optional[str]:
    """
    Return a copy of bpl_text with the assert {:id "boogie_id"} statement
    commented out.  Returns None if the assertion is not found.
    """
    lines = bpl_text.splitlines(keepends=True)
    span = _find_assert_span([l.rstrip("\n") for l in lines], boogie_id)
    if span is None:
        return None
    start, end = span
    for i in range(start, end + 1):
        lines[i] = "// REMOVED: " + lines[i]
    return "".join(lines)


# ---------------------------------------------------------------------------
# Boogie output parsing
# ---------------------------------------------------------------------------


def _parse_failing_bpl_lines(boogie_errors: list[str]) -> list[int]:
    """Extract BPL line numbers from Boogie error strings."""
    lines = []
    for err in boogie_errors:
        m = re.search(r'\((\d+),\d+\):\s*Error', err)
        if m:
            lines.append(int(m.group(1)))
    return lines


def _find_assert_at_bpl_line(bpl_lines: list[str], line_no: int) -> Optional[str]:
    """
    Given a 1-based BPL line number from a Boogie error, scan backwards to
    find the assert statement that owns that line and return its full text.
    """
    # line_no is 1-based
    idx = line_no - 1
    idx = min(idx, len(bpl_lines) - 1)

    # Scan backwards to find the start of the assert containing this line
    start = idx
    while start > 0:
        if re.search(r'\bassert\b', bpl_lines[start]):
            break
        start -= 1

    if not re.search(r'\bassert\b', bpl_lines[start]):
        return None

    # Scan forward to the semicolon
    end = start
    while end < len(bpl_lines) and ";" not in bpl_lines[end]:
        end += 1

    return " ".join(bpl_lines[start:end + 1]).strip().rstrip(";").strip()


# ---------------------------------------------------------------------------
# Existential parsing and matching
# ---------------------------------------------------------------------------


def _parse_exists_expr(text: str) -> tuple[list[str], list[Expr]]:
    """
    Parse '(exists x: T :: { trigger } body)'.
    Returns (bound_var_names, trigger_exprs).
    Trigger exprs are empty if no trigger block is present.
    """
    text = text.strip()
    if text.startswith("(") and text.endswith(")"):
        text = text[1:-1].strip()
    m = re.match(r"exists\s*(?:<[^>]*>\s*)?(.*?)\s*::\s*(.*)", text, re.DOTALL)
    if not m:
        return [], []
    bound_vars = _extract_binders(m.group(1))
    after_colons = m.group(2).strip()
    # Extract trigger block: { ... } immediately after ::
    trigger_exprs: list[Expr] = []
    m_trigger = re.match(r"(\s*(?:\{[^}]*\}\s*)+)", after_colons)
    if m_trigger:
        trigger_exprs = _parse_triggers(m_trigger.group(1))
    return bound_vars, trigger_exprs


# ---------------------------------------------------------------------------
# Core classification
# ---------------------------------------------------------------------------


async def classify_witness_async(
    pool: DafnyPool,
    dfy_path: Path,
    boogie_id: str,
    timeout: int = 30,
    bpl_text: str = "",
) -> WitnessResult:
    """
    Check whether the assertion identified by boogie_id is providing an
    existential witness.

    Removes the assertion from the BPL, runs Boogie on the result, then
    checks whether any newly failing VCs are existential formulas.

    dfy_path: the original verified .dfy file (used to generate BPL if needed)
    boogie_id: the boogieId of the assertion to classify (e.g. "id92")
    bpl_text: pre-generated BPL text (skips Dafny run if provided)
    """
    if not bpl_text:
        bpl_text, _ = await generate_bpl_async(pool, dfy_path, timeout)

    # Get the assertion expression from the original BPL (before removal)
    assertion_expr = find_assert_expr_in_bpl(bpl_text, boogie_id)
    if assertion_expr is None:
        return WitnessResult(
            boogie_id=boogie_id,
            confidence="none",
            exists_assertions=[],
            note=f'could not find assert with id "{boogie_id}" in BPL',
        )

    # Remove the assertion from the BPL
    modified_bpl = _remove_assert(bpl_text, boogie_id)
    if modified_bpl is None:
        return WitnessResult(
            boogie_id=boogie_id,
            confidence="none",
            exists_assertions=[],
            note=f'could not locate assert span for "{boogie_id}" in BPL',
        )

    # Run Boogie on the modified BPL
    with tempfile.NamedTemporaryFile(suffix=".bpl", mode="w", delete=False) as f:
        f.write(modified_bpl)
        tmp_bpl = Path(f.name)

    try:
        boogie_output = await pool.run_boogie(
            BoogieArgs(bpl_file=tmp_bpl, time_limit=timeout)
        )
    finally:
        tmp_bpl.unlink(missing_ok=True)

    if boogie_output.result == "pass":
        return WitnessResult(
            boogie_id=boogie_id,
            confidence="none",
            exists_assertions=[],
            note="removing assertion did not cause any Boogie failures",
        )

    # Find which BPL lines failed
    failing_lines = _parse_failing_bpl_lines(boogie_output.errors)
    if not failing_lines:
        return WitnessResult(
            boogie_id=boogie_id,
            confidence="none",
            exists_assertions=[],
            note="could not parse failing line numbers from Boogie output",
        )

    # Find the failing assert texts and check for existentials
    bpl_lines = modified_bpl.splitlines()
    exists_assertions: list[str] = []
    for line_no in failing_lines:
        text = _find_assert_at_bpl_line(bpl_lines, line_no)
        if text and re.search(r'\bexists\b', text, re.IGNORECASE):
            exists_assertions.append(text)

    if not exists_assertions:
        return WitnessResult(
            boogie_id=boogie_id,
            confidence="none",
            exists_assertions=[],
            note=f"failing VCs at lines {failing_lines} do not contain existential formulas",
        )

    # Try to match assertion subterms against the trigger of each failing existential
    for raw in exists_assertions:
        bound_vars, trigger_exprs = _parse_exists_expr(raw)
        if not trigger_exprs:
            continue
        assertion_subterms = subterms(assertion_expr)
        for trigger in trigger_exprs:
            for subterm in assertion_subterms:
                sigma: dict[str, Expr] = {}
                if match(subterm, trigger, set(bound_vars), sigma):
                    return WitnessResult(
                        boogie_id=boogie_id,
                        confidence="high",
                        exists_assertions=exists_assertions,
                        matched_exists=raw,
                        note=(
                            f"assertion subterm {subterm!r} matches trigger of failing "
                            f"existential: {raw!r}  "
                            f"with substitution {{{', '.join(f'{k}→{v!r}' for k, v in sigma.items())}}}"
                        ),
                    )

    return WitnessResult(
        boogie_id=boogie_id,
        confidence="low",
        exists_assertions=exists_assertions,
        note=f"found {len(exists_assertions)} failing existential VC(s); no trigger match found",
    )


def classify_witness(
    pool: DafnyPool,
    dfy_path: Path,
    boogie_id: str,
    timeout: int = 30,
    bpl_text: str = "",
) -> WitnessResult:
    return asyncio.run(
        classify_witness_async(pool, dfy_path, boogie_id, timeout, bpl_text)
    )


# ---------------------------------------------------------------------------
# CLI
# ---------------------------------------------------------------------------


def _witness_to_dict(r: WitnessResult) -> dict:
    d: dict = {
        "boogie_id": r.boogie_id,
        "confidence": r.confidence,
        "exists_assertions": r.exists_assertions,
        "note": r.note,
    }
    if r.matched_exists is not None:
        d["matched_exists"] = r.matched_exists
    return d


if __name__ == "__main__":
    import argparse
    import sys

    parser = argparse.ArgumentParser(
        description="Detect existential witness role of an essential assertion."
    )
    parser.add_argument("--dfy", required=True, help="Path to verified .dfy file")
    parser.add_argument("--boogie-id", required=True, help="boogieId of the assertion (e.g. id92)")
    parser.add_argument("--timeout", type=int, default=30)
    parser.add_argument("--bpl", default="", help="Pre-generated BPL file path (skip Dafny run)")
    parser.add_argument("--max-concurrency", type=int, default=1)
    args = parser.parse_args()

    pool = DafnyPool(max_concurrency=args.max_concurrency)
    bpl_text = Path(args.bpl).read_text() if args.bpl else ""

    result = asyncio.run(
        classify_witness_async(pool, Path(args.dfy), args.boogie_id, args.timeout, bpl_text)
    )
    print(json.dumps(_witness_to_dict(result), indent=2))
    sys.exit(0 if result.confidence != "none" else 1)

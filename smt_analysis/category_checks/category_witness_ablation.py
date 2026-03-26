#!/usr/bin/env python3
"""
Ablation-based existential witness detector.

Removes the assertion identified by boogie_id from the BPL, runs Boogie on the
modified program, then inspects the failing conditions to see if any of them is
an existential formula.

Two confidence levels:

  high — a failing condition is existential AND a subterm of the assertion
         matches one of its triggers
  low  — a failing condition is existential but no trigger match found
  none — no failing conditions are existential (or Boogie still passes)

This approach is complementary to the static scan in category_witness.py.
It catches cases where the existential proof burden is visible as a direct
Boogie error (e.g. a postcondition `ensures exists ...`), but misses cases
where the existential is hidden inside a predicate definition.

Usage:
    python3 -m smt_analysis.category_checks.category_witness_ablation \\
        --dfy smt_analysis/results/0024_1091_A/verified.dfy \\
        --boogie-id id48
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
    _trigger_specificity,
    find_assert_expr_in_bpl,
    generate_bpl_async,
    match,
    subterms,
)

WitnessConfidence = Literal["none", "low", "high"]


@dataclass
class AblationWitnessResult:
    """
    Result of the ablation-based existential witness check.

    confidence:
      "none" — Boogie still passes after removing the assertion, or no
               failing condition contains an existential
      "low"  — a failing condition is existential but no trigger match found
      "high" — a failing condition is existential AND a subterm of the
               assertion matches one of its triggers
    """

    boogie_id: str
    confidence: WitnessConfidence
    failing_exists: list[str]   # text of failing existential conditions
    matched_trigger: Optional[str] = None
    note: str = ""


# ---------------------------------------------------------------------------
# BPL manipulation
# ---------------------------------------------------------------------------


def remove_assertion_from_bpl(bpl_text: str, boogie_id: str) -> str:
    """
    Remove the assertion with the given boogie_id from the BPL text.
    Handles multi-line assertions (collects up to the semicolon).
    """
    lines = bpl_text.splitlines()
    id_pat = re.compile(
        r"assert\s+(?:\{[^}]*\}\s*)*\{:id\s+\"" + re.escape(boogie_id) + r"\""
    )
    result: list[str] = []
    i = 0
    while i < len(lines):
        if id_pat.search(lines[i]):
            # Collect the full statement up to the semicolon
            collected = lines[i]
            j = i + 1
            while ";" not in collected and j < len(lines):
                collected += " " + lines[j]
                j += 1
            result.append(f"    // [ablated {boogie_id}]")
            i = j
        else:
            result.append(lines[i])
            i += 1
    return "\n".join(result)


# ---------------------------------------------------------------------------
# Boogie output parsing
# ---------------------------------------------------------------------------


def _parse_failing_condition_lines(boogie_output: str) -> list[int]:
    """
    Extract line numbers of failing conditions from Boogie output.

    Collects:
    - Direct assertion failures: "(line,col): Error BP5001"
    - Postcondition locations:   "(line,col): Related location: this is the postcondition"
    - Loop invariant locations:  "(line,col): Related location: this is the loop invariant"
    """
    lines = []
    # Direct assertion failure
    for m in re.finditer(r"\((\d+),\d+\):\s+Error\s+BP5001", boogie_output):
        lines.append(int(m.group(1)))
    # Postcondition / invariant "related location"
    for m in re.finditer(
        r"\((\d+),\d+\):\s+Related location:\s+this is the (postcondition|loop invariant)",
        boogie_output,
    ):
        lines.append(int(m.group(1)))
    return lines


def _get_statement_at_line(bpl_text: str, lineno: int) -> str:
    """
    Return the full BPL statement starting at lineno (1-based),
    collected up to the semicolon.
    """
    lines = bpl_text.splitlines()
    idx = lineno - 1
    if idx < 0 or idx >= len(lines):
        return ""
    text = lines[idx]
    j = idx + 1
    while ";" not in text and j < len(lines):
        text += " " + lines[j]
        j += 1
    return text.strip()


# ---------------------------------------------------------------------------
# Existential check + trigger matching on a failing condition
# ---------------------------------------------------------------------------


def _parse_exists_trigger(condition_text: str) -> tuple[list[str], list[Expr]]:
    """
    If condition_text contains an exists formula, return (bound_vars, triggers).
    Returns ([], []) if no exists is found or it has no triggers.
    """
    m = re.search(r"\bexists\s*(?:<[^>]*>\s*)?(.*?)\s*::\s*", condition_text, re.DOTALL)
    if not m:
        return [], []
    bound_vars = _extract_binders(m.group(1))
    after = condition_text[m.end():]
    m_trigger = re.match(r"(\s*(?:\{[^}]*\}\s*)+)", after)
    if not m_trigger:
        return bound_vars, []
    return bound_vars, _parse_triggers(m_trigger.group(1))


# ---------------------------------------------------------------------------
# Core classification
# ---------------------------------------------------------------------------


async def classify_witness_ablation_async(
    pool: DafnyPool,
    dfy_path: Path,
    boogie_id: str,
    timeout: int = 30,
    bpl_text: str = "",
) -> AblationWitnessResult:
    """
    Ablation-based existential witness check.

    1. Removes the assertion from the BPL.
    2. Runs Boogie on the modified program.
    3. Inspects failing conditions for existential formulas.
    4. Tries trigger matching between the original assertion and the failing
       existential for high confidence.
    """
    if not bpl_text:
        bpl_text, _ = await generate_bpl_async(pool, dfy_path, timeout)

    assertion_expr = find_assert_expr_in_bpl(bpl_text, boogie_id)
    if assertion_expr is None:
        return AblationWitnessResult(
            boogie_id=boogie_id,
            confidence="none",
            failing_exists=[],
            note=f'could not find assert with id "{boogie_id}" in BPL',
        )

    modified_bpl = remove_assertion_from_bpl(bpl_text, boogie_id)

    with tempfile.NamedTemporaryFile(suffix=".bpl", mode="w", delete=False) as f:
        f.write(modified_bpl)
        tmp_path = Path(f.name)

    try:
        boogie_result = await pool.run_boogie(
            BoogieArgs(bpl_file=tmp_path, time_limit=timeout)
        )
    finally:
        tmp_path.unlink(missing_ok=True)

    if boogie_result.result == "pass":
        return AblationWitnessResult(
            boogie_id=boogie_id,
            confidence="none",
            failing_exists=[],
            note="Boogie still passes after removing the assertion — not essential at BPL level",
        )

    failing_lines = _parse_failing_condition_lines(boogie_result.raw_output)
    if not failing_lines:
        return AblationWitnessResult(
            boogie_id=boogie_id,
            confidence="none",
            failing_exists=[],
            note=f"Boogie failed but could not parse failing condition line numbers\n{boogie_result.raw_output[:200]}",
        )

    # Collect failing conditions that contain exists
    failing_exists: list[str] = []
    for lineno in dict.fromkeys(failing_lines):  # deduplicate, preserve order
        text = _get_statement_at_line(bpl_text, lineno)
        if re.search(r"\bexists\b", text, re.IGNORECASE):
            failing_exists.append(text)

    if not failing_exists:
        return AblationWitnessResult(
            boogie_id=boogie_id,
            confidence="none",
            failing_exists=[],
            note=(
                f"failing conditions at lines {failing_lines} do not contain "
                f"existential formulas"
            ),
        )

    # Try trigger matching for high confidence
    assertion_subterms = subterms(assertion_expr)
    for cond in failing_exists:
        bound_vars, triggers = _parse_exists_trigger(cond)
        bound = set(bound_vars)
        for trigger in triggers:
            if _trigger_specificity(trigger, bound) == 0:
                continue
            for sub in assertion_subterms:
                sigma: dict[str, Expr] = {}
                if match(sub, trigger, bound, sigma) and sigma:
                    return AblationWitnessResult(
                        boogie_id=boogie_id,
                        confidence="high",
                        failing_exists=failing_exists,
                        matched_trigger=repr(trigger),
                        note=(
                            f"assertion subterm {sub!r} matches trigger {trigger!r} "
                            f"of failing existential "
                            f"(substitution: "
                            f"{{{', '.join(f'{k}→{v!r}' for k, v in sigma.items())}}})"
                        ),
                    )

    return AblationWitnessResult(
        boogie_id=boogie_id,
        confidence="low",
        failing_exists=failing_exists,
        note=(
            f"found {len(failing_exists)} failing existential condition(s) "
            f"but no trigger match found"
        ),
    )


def classify_witness_ablation(
    pool: DafnyPool,
    dfy_path: Path,
    boogie_id: str,
    timeout: int = 30,
    bpl_text: str = "",
) -> AblationWitnessResult:
    return asyncio.run(
        classify_witness_ablation_async(pool, dfy_path, boogie_id, timeout, bpl_text)
    )


# ---------------------------------------------------------------------------
# CLI
# ---------------------------------------------------------------------------


def _result_to_dict(r: AblationWitnessResult) -> dict:
    d: dict = {
        "boogie_id": r.boogie_id,
        "confidence": r.confidence,
        "failing_exists": r.failing_exists,
        "note": r.note,
    }
    if r.matched_trigger is not None:
        d["matched_trigger"] = r.matched_trigger
    return d


if __name__ == "__main__":
    import argparse
    import sys

    parser = argparse.ArgumentParser(
        description="Ablation-based existential witness detection via Boogie."
    )
    parser.add_argument("--dfy", required=True, help="Path to verified .dfy file")
    parser.add_argument("--boogie-id", required=True, help="boogieId of the assertion")
    parser.add_argument("--timeout", type=int, default=30)
    parser.add_argument("--bpl", default="", help="Pre-generated BPL file path")
    parser.add_argument("--max-concurrency", type=int, default=1)
    args = parser.parse_args()

    pool = DafnyPool(max_concurrency=args.max_concurrency)
    bpl_text = Path(args.bpl).read_text() if args.bpl else ""

    result = asyncio.run(
        classify_witness_ablation_async(
            pool, Path(args.dfy), args.boogie_id, args.timeout, bpl_text
        )
    )
    print(json.dumps(_result_to_dict(result), indent=2))
    sys.exit(0 if result.confidence != "none" else 1)

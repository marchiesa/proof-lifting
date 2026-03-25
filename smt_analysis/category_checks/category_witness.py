#!/usr/bin/env python3
"""
Existential witness detector for essential assertions (A1/A3 categories).

For a given essential assertion (identified by boogieId), scans the BPL for
(exists ...) assertions that appear after it and checks whether the assertion
expression directly matches the existential body, giving two confidence levels:

  high — assertion expression matches the body of a following (exists x :: P(x))
         via one-sided pattern matching: the assertion IS P(witness)
  low  — at least one (exists ...) assertion follows this one in the BPL,
         but no direct body match was found
  none — no (exists ...) assertions appear after this assertion in the BPL

Usage:
    python3 -m smt_analysis.category_checks.category_witness \\
        --dfy smt_analysis/results/0006_1017_A/verified.dfy \\
        --boogie-id id92
"""

from __future__ import annotations

import json
import re
from dataclasses import dataclass
from pathlib import Path
from typing import Literal, Optional

from smt_analysis.category_checks.category_ematching import (
    Expr,
    _extract_binders,
    find_assert_expr_in_bpl,
    generate_bpl,
    match,
    parse_expr,
)

WitnessConfidence = Literal["none", "low", "high"]


@dataclass
class WitnessResult:
    """
    Result of checking whether an assertion is providing an existential witness.

    confidence:
      "none" — no existential assertions found after this assertion in BPL
      "low"  — at least one (exists ...) assertion appears after this one, but
               the assertion expression does not match any existential body
      "high" — assertion expression matches the body of a following (exists ...)
               via one-sided pattern matching (assertion IS P(witness) for some
               exists x :: P(x))
    """

    boogie_id: str
    confidence: WitnessConfidence
    exists_assertions: list[str]  # raw text of exists assertions found after this one
    matched_exists_body: Optional[str] = None  # the body that matched (high confidence)
    note: str = ""


def _line_of_assertion(bpl_text: str, boogie_id: str) -> Optional[int]:
    """Return the 1-based line number of the assert {:id "boogie_id"} in BPL."""
    pattern = re.compile(
        r'assert\s+(?:\{[^}]*\}\s*)*\{:id\s+"' + re.escape(boogie_id) + r'"'
    )
    for i, line in enumerate(bpl_text.splitlines(), start=1):
        if pattern.search(line):
            return i
    return None


def _find_exists_assertions_after(
    bpl_text: str, after_line: int
) -> list[tuple[str, list[str], Optional[Expr]]]:
    """
    Scan BPL assert statements after `after_line` for ones containing (exists ...).
    Returns list of (raw_assert_expr_text, bound_vars, parsed_body).
    """
    results = []
    lines = bpl_text.splitlines()
    # after_line is 1-based; lines[after_line] is the first line after the assertion
    i = after_line
    assert_re = re.compile(r'\bassert\b(?:\s*\{[^}]*\})*\s*(.*)')
    while i < len(lines):
        m = assert_re.search(lines[i])
        if m:
            expr_text = m.group(1)
            j = i + 1
            while ";" not in expr_text and j < len(lines):
                expr_text += " " + lines[j]
                j += 1
            expr_text = expr_text.strip().rstrip(";").strip()
            if re.search(r'\bexists\b', expr_text, re.IGNORECASE):
                bound_vars, body = _parse_exists_expr(expr_text)
                results.append((expr_text, bound_vars, body))
        i += 1
    return results


def _parse_exists_expr(text: str) -> tuple[list[str], Optional[Expr]]:
    """
    Parse '(exists x1: T1, x2: T2 :: body)' or 'exists x :: body'.
    Returns (bound_var_names, parsed_body_expr).
    """
    text = text.strip()
    if text.startswith("(") and text.endswith(")"):
        text = text[1:-1].strip()
    m = re.match(r'exists\s*(?:<[^>]*>\s*)?(.*?)\s*::\s*(.*)', text, re.DOTALL)
    if not m:
        return [], None
    bound_vars = _extract_binders(m.group(1))
    body_expr = parse_expr(m.group(2).strip())
    return bound_vars, body_expr


def classify_witness(
    assertion_expr: Expr,
    bpl_text: str,
    boogie_id: str,
) -> WitnessResult:
    """
    Check whether `assertion_expr` is providing an existential witness.

    Scans BPL assertions that appear after the removed assertion for (exists ...)
    formulas, then tries to match the assertion expression against each body.
    """
    assert_line = _line_of_assertion(bpl_text, boogie_id)
    if assert_line is None:
        return WitnessResult(
            boogie_id=boogie_id,
            confidence="none",
            exists_assertions=[],
            note=f'could not locate assert {{:id "{boogie_id}"}} in BPL',
        )

    exists_found = _find_exists_assertions_after(bpl_text, assert_line)
    if not exists_found:
        return WitnessResult(
            boogie_id=boogie_id,
            confidence="none",
            exists_assertions=[],
            note="no (exists ...) assertions found after this assertion in BPL",
        )

    raw_texts = [e[0] for e in exists_found]

    for raw, bound_vars, body in exists_found:
        if body is None:
            continue
        sigma: dict[str, Expr] = {}
        if match(assertion_expr, body, set(bound_vars), sigma):
            return WitnessResult(
                boogie_id=boogie_id,
                confidence="high",
                exists_assertions=raw_texts,
                matched_exists_body=raw,
                note=(
                    f"assertion matches body of: {raw!r}  "
                    f"with substitution {{{', '.join(f'{k}→{v!r}' for k, v in sigma.items())}}}"
                ),
            )

    return WitnessResult(
        boogie_id=boogie_id,
        confidence="low",
        exists_assertions=raw_texts,
        note=f"found {len(exists_found)} exists assertion(s) after this one; no direct body match",
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
    if r.matched_exists_body is not None:
        d["matched_exists_body"] = r.matched_exists_body
    return d


if __name__ == "__main__":
    import argparse
    import sys

    parser = argparse.ArgumentParser(
        description="Detect existential witness role of an essential assertion."
    )
    parser.add_argument("--dfy", required=True, help="Path to verified .dfy file")
    parser.add_argument(
        "--boogie-id", required=True, help="boogieId of the assertion (e.g. id92)"
    )
    parser.add_argument("--timeout", type=int, default=30)
    parser.add_argument(
        "--bpl", default="", help="Pre-generated BPL file path (skip Dafny run)"
    )
    args = parser.parse_args()

    bpl_text = Path(args.bpl).read_text() if args.bpl else ""
    if not bpl_text:
        bpl_text, _ = generate_bpl(Path(args.dfy), args.timeout)

    assertion_expr = find_assert_expr_in_bpl(bpl_text, args.boogie_id)
    if assertion_expr is None:
        print(
            json.dumps(
                {
                    "error": f'could not find assert with id "{args.boogie_id}" in BPL'
                }
            )
        )
        sys.exit(1)

    result = classify_witness(assertion_expr, bpl_text, args.boogie_id)
    print(json.dumps(_witness_to_dict(result), indent=2))
    sys.exit(0 if result.confidence != "none" else 1)

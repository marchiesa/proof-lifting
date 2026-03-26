#!/usr/bin/env python3
"""
Existential witness detector for essential assertions.

Statically scans the BPL for all existential proof obligations
(assert/ensures/invariant containing `exists`) and checks whether any subterm
of the assertion matches either:

  - a trigger of the existential (high confidence via E-matching)
  - a subterm of the existential body with bound vars as pattern variables
    (high confidence via direct witness matching)

Two confidence levels:

  high — a subterm of the assertion matches a trigger or body subterm of an
         existential proof obligation, with bound vars substituted
  low  — existential proof obligations exist in the BPL but no match found
  none — no existential proof obligations found in the BPL

Usage:
    python3 -m smt_analysis.category_checks.category_witness \\
        --dfy smt_analysis/results/0006_1017_A/verified.dfy \\
        --boogie-id id92
"""

from __future__ import annotations

import asyncio
import json
import re
from dataclasses import dataclass
from pathlib import Path
from typing import Literal, Optional

from run_dafny import DafnyPool
from smt_analysis.category_checks.category_ematching import (
    Expr,
    _extract_binders,
    _parse_triggers,
    _trigger_specificity,
    find_assert_expr_in_bpl,
    generate_bpl_async,
    match,
    parse_expr,
    subterms,
)

WitnessConfidence = Literal["none", "low", "high"]


@dataclass
class BplExistential:
    """An existential proof obligation extracted from a BPL file."""

    kind: str  # "assert", "ensures", "invariant"
    bound_vars: list[str]
    triggers: list[Expr]  # may be empty if Dafny emitted no triggers
    body_terms: list[Expr]  # subterms of the existential body (for direct matching)
    raw_trigger: str  # raw trigger text (may be "")
    raw_body: str  # raw body text after triggers
    line: int


@dataclass
class WitnessResult:
    """
    Result of checking whether an assertion is providing an existential witness.

    confidence:
      "none" — no existential proof obligations found in BPL
      "low"  — existential proof obligations exist but no match found
      "high" — a subterm of the assertion matches a trigger or body term of an
               existential (i.e. the assertion plausibly provides a concrete witness)
    """

    boogie_id: str
    confidence: WitnessConfidence
    exists_obligations: list[str]  # summary strings of found existentials
    matched_exists: Optional[BplExistential] = None
    note: str = ""


# ---------------------------------------------------------------------------
# Existential proof obligation extractor
# ---------------------------------------------------------------------------


def _collect_block(lines: list[str], start: int) -> tuple[str, int]:
    """
    Collect a complete BPL statement starting at `start` by balancing
    parentheses. Returns (joined_block_text, next_line_index).
    """
    block_lines: list[str] = []
    depth = 0
    j = start
    while j < len(lines):
        block_lines.append(lines[j])
        depth += lines[j].count("(") - lines[j].count(")")
        j += 1
        if depth <= 0 and block_lines:
            break
    return " ".join(block_lines), j


def _parse_existential_body(
    after_colons: str, bound_vars: list[str]
) -> tuple[str, str, list[Expr]]:
    """
    Split the text after `::` into (trigger_raw, body_raw, body_subterms).
    Skips any leading `{ ... }` trigger blocks, then parses the body.

    The body may be a conjunction of clauses separated by &&/||/==>. We split
    on these infix operators and parse each clause individually, collecting all
    subterms across the body. This catches function calls like
    `ValidChoice(...)` that would otherwise be hidden behind `<=` / `&&`.
    """
    text = after_colons.strip()
    # Collect trigger blocks { ... }
    trigger_raw = ""
    m_trigger = re.match(r"(\s*(?:\{[^}]*\}\s*)+)", text)
    if m_trigger:
        trigger_raw = m_trigger.group(1)
        text = text[m_trigger.end() :].strip()
    # Strip trailing semicolon / closing paren artifacts
    body_raw = text.rstrip(");").strip()
    # Split body on boolean operators (respecting paren depth)
    clauses = _split_body_clauses(body_raw)
    # Parse each clause and gather subterms
    all_subterms: list[Expr] = []
    seen: set[str] = set()
    for clause in clauses:
        expr = parse_expr(clause.strip())
        if expr is not None:
            for t in subterms(expr):
                key = repr(t)
                if key not in seen:
                    seen.add(key)
                    all_subterms.append(t)
    return trigger_raw, body_raw, all_subterms


def _split_body_clauses(body: str) -> list[str]:
    """
    Split a BPL boolean expression on top-level &&/||/==> operators,
    respecting parenthesis depth so that nested sub-expressions are kept whole.
    """
    clauses: list[str] = []
    current: list[str] = []
    depth = 0
    i = 0
    while i < len(body):
        ch = body[i]
        if ch in "([":
            depth += 1
            current.append(ch)
            i += 1
        elif ch in ")]":
            depth -= 1
            current.append(ch)
            i += 1
        elif depth == 0 and body[i : i + 2] in ("&&", "||"):
            clauses.append("".join(current).strip())
            current = []
            i += 2
        elif depth == 0 and body[i : i + 3] == "==>":
            clauses.append("".join(current).strip())
            current = []
            i += 3
        else:
            current.append(ch)
            i += 1
    if current:
        clauses.append("".join(current).strip())
    return [c for c in clauses if c]


def _extract_forall_bound_vars(block: str) -> list[str]:
    """Extract bound variable names from the outermost `forall` in block."""
    m = re.search(r"\bforall\s*(?:<[^>]*>\s*)?(.*?)\s*::", block, re.DOTALL)
    return _extract_binders(m.group(1)) if m else []


def extract_existentials(bpl_text: str) -> list[BplExistential]:
    """
    Extract existential formulas that may require a witness from a BPL file.

    Two contexts are scanned:

    1. Proof-obligation contexts (assert/ensures/invariant, non-free):
       These are direct existential obligations. Bound variables of the exists
       are used as pattern variables for matching.

    2. Axiom bodies containing `exists` with triggers:
       When Dafny compiles a predicate like `InSeq(x, s) == exists i :: s[i] == x`,
       the inner `exists` is embedded in a `forall` axiom and carries a trigger.
       An assertion that fires this trigger (e.g. `s[w] == x`) provides the witness.
       Here ALL bound variables of the enclosing block (outer forall vars + exists vars)
       are used as pattern variables so the trigger match can succeed.
    """
    existentials: list[BplExistential] = []
    lines = bpl_text.splitlines()

    po_re = re.compile(r"^\s*(assert|ensures|invariant)\b")
    axiom_re = re.compile(r"^\s*axiom\b")
    free_re = re.compile(r"^\s*free\s+")
    defn_comment_re = re.compile(r"//\s*definition axiom for _module\.")

    i = 0
    is_user_defn_axiom = False  # set True when we see the definition-axiom comment
    while i < len(lines):
        line = lines[i]
        stripped = line.strip()

        # Track whether the next axiom line is a user predicate definition
        if defn_comment_re.search(stripped):
            is_user_defn_axiom = True
            i += 1
            continue

        if stripped.startswith("//") or free_re.match(line):
            i += 1
            continue

        kind_m = po_re.match(line)
        # Only scan axioms that define user predicates — identified by the comment
        # "// definition axiom for _module.__default.*" on the preceding line.
        is_axiom = bool(axiom_re.match(line)) and is_user_defn_axiom

        if not kind_m and not is_axiom:
            is_user_defn_axiom = False
            i += 1
            continue

        kind = kind_m.group(1) if kind_m else "axiom"
        block, next_i = _collect_block(lines, i)

        if not re.search(r"\bexists\b", block, re.IGNORECASE):
            i = next_i
            continue

        # For axiom blocks: collect outer forall bound vars to use in matching
        outer_forall_vars = _extract_forall_bound_vars(block) if is_axiom else []

        # Find each `exists` subformula in this block.
        # Binders may contain ':' (e.g. "ny#3: int"), so we match up to '::'
        # (double colon) using a lazy match.
        for m_e in re.finditer(
            r"\bexists\s*(?:<[^>]*>\s*)?(.*?)\s*::\s*", block, re.DOTALL
        ):
            exists_bound_vars = _extract_binders(m_e.group(1))
            # For axiom-embedded existentials, pattern matching uses all bound vars
            # in scope (outer forall + inner exists) so the trigger can match
            # against concrete assertion subterms.
            all_bound_vars = outer_forall_vars + exists_bound_vars
            after = block[m_e.end() :]
            trigger_raw, body_raw, body_subterms = _parse_existential_body(
                after, all_bound_vars
            )
            triggers = _parse_triggers(trigger_raw) if trigger_raw else []
            # Only include if we have something to match against
            if triggers or (body_subterms and not is_axiom):
                existentials.append(
                    BplExistential(
                        kind=kind,
                        bound_vars=all_bound_vars,
                        triggers=triggers,
                        body_terms=body_subterms if not is_axiom else [],
                        raw_trigger=trigger_raw.strip(),
                        raw_body=body_raw[:120],  # truncate for display
                        line=i + 1,
                    )
                )

        is_user_defn_axiom = False  # consumed — reset for next line
        i = next_i

    return existentials


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

    Statically scans the BPL for existential proof obligations and checks
    whether any subterm of the assertion matches a trigger or body term of one.
    No ablation run is required.
    """
    if not bpl_text:
        bpl_text, _ = await generate_bpl_async(pool, dfy_path, timeout)

    assertion_expr = find_assert_expr_in_bpl(bpl_text, boogie_id)
    if assertion_expr is None:
        return WitnessResult(
            boogie_id=boogie_id,
            confidence="none",
            exists_obligations=[],
            note=f'could not find assert with id "{boogie_id}" in BPL',
        )

    existentials = extract_existentials(bpl_text)

    # Separate direct proof obligations (assert/ensures/invariant) from axiom-embedded ones.
    # Only direct obligations contribute to the "low" fallback — axiom existentials are
    # extremely common in the prelude and would make "low" meaningless if always present.
    direct_obligations = [e for e in existentials if e.kind != "axiom"]
    all_obligations = existentials  # both kinds are tried for trigger/body matching

    obligation_summaries = [
        f"{e.kind}(line {e.line}): triggers={e.raw_trigger!r} body={e.raw_body!r}"
        for e in all_obligations
    ]

    assertion_subterms = subterms(assertion_expr)

    for ex in all_obligations:
        bound = set(ex.bound_vars)

        # 1. Try trigger matching (E-matching path — works for both direct and axiom exists)
        # Require sigma non-empty: at least one bound variable must be concretely matched.
        for trigger in ex.triggers:
            for sub in assertion_subterms:
                sigma: dict[str, Expr] = {}
                if match(sub, trigger, bound, sigma) and sigma:
                    return WitnessResult(
                        boogie_id=boogie_id,
                        confidence="high",
                        exists_obligations=obligation_summaries,
                        matched_exists=ex,
                        note=(
                            f"assertion subterm {sub!r} matches trigger {trigger!r} "
                            f"of {ex.kind} existential at BPL line {ex.line} "
                            f"(substitution: "
                            f"{{{', '.join(f'{k}→{v!r}' for k, v in sigma.items())}}})"
                        ),
                    )

        # 2. Try body term matching (direct witness path — only for direct proof obligations)
        # Axiom bodies are not used here to avoid false positives from prelude axioms.
        # Skip body terms that are just bare bound variables (they match anything trivially).
        # Also require sigma non-empty: a useful body match must instantiate at least one
        # bound variable (otherwise it just means both share a constant/variable, not a witness).
        for body_term in ex.body_terms:
            if _trigger_specificity(body_term, bound) == 0:
                continue
            for sub in assertion_subterms:
                sigma = {}
                if match(sub, body_term, bound, sigma) and sigma:
                    return WitnessResult(
                        boogie_id=boogie_id,
                        confidence="high",
                        exists_obligations=obligation_summaries,
                        matched_exists=ex,
                        note=(
                            f"assertion subterm {sub!r} matches body term {body_term!r} "
                            f"of {ex.kind} existential at BPL line {ex.line} "
                            f"(substitution: "
                            f"{{{', '.join(f'{k}→{v!r}' for k, v in sigma.items())}}})"
                        ),
                    )

    # "low": direct existential proof obligations exist in this BPL but none matched
    # (the assertion may still provide a witness in a non-obvious way)
    # "none": no direct proof obligations — no evidence this assertion is a witness
    if direct_obligations:
        return WitnessResult(
            boogie_id=boogie_id,
            confidence="none",
            exists_obligations=obligation_summaries,
            note=(
                f"found {len(direct_obligations)} direct existential proof obligation(s) "
                f"but no trigger or body term matched any assertion subterm"
            ),
        )
    return WitnessResult(
        boogie_id=boogie_id,
        confidence="none",
        exists_obligations=[],
        note="no direct existential proof obligations found (axiom-embedded existentials did not match)",
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
        "exists_obligations": r.exists_obligations,
        "note": r.note,
    }
    if r.matched_exists is not None:
        ex = r.matched_exists
        d["matched_exists"] = {
            "kind": ex.kind,
            "bound_vars": ex.bound_vars,
            "raw_trigger": ex.raw_trigger,
            "raw_body": ex.raw_body,
            "line": ex.line,
        }
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
    parser.add_argument("--max-concurrency", type=int, default=1)
    args = parser.parse_args()

    pool = DafnyPool(max_concurrency=args.max_concurrency)
    bpl_text = Path(args.bpl).read_text() if args.bpl else ""

    result = asyncio.run(
        classify_witness_async(
            pool, Path(args.dfy), args.boogie_id, args.timeout, bpl_text
        )
    )
    print(json.dumps(_witness_to_dict(result), indent=2))
    sys.exit(0 if result.confidence != "none" else 1)

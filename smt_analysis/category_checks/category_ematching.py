#!/usr/bin/env python3
"""
E-matching category detector for essential assertions.

For a given essential assertion (identified by boogieId), generates a BPL
from the *original* verified file and checks which quantifier trigger the
assertion expression directly fires, classifying as:

  ematching-axiom   — trigger is from a prelude axiom (forall in axiom block)
  ematching-user    — trigger is from a user forall (assume forall in procedure)
  ematching-exists  — assertion provides an existential witness
  unknown           — no direct trigger match found

Usage:
    python3 -m smt_analysis.category_checks.category_ematching \\
        --dfy smt_analysis/results/0006_1017_A/verified.dfy \\
        --boogie-id id92
"""

from __future__ import annotations
from typing import Dict, Literal, Union

import asyncio
import json
import re
import sys
import tempfile
from dataclasses import dataclass
from pathlib import Path
from typing import Optional

PROJ_ROOT = Path(__file__).resolve().parents[2]
if str(PROJ_ROOT) not in sys.path:
    sys.path.insert(0, str(PROJ_ROOT))

from run_dafny import CustomDafnyArgs, DafnyPool  # noqa: E402


# ---------------------------------------------------------------------------
# Expression tree
# ---------------------------------------------------------------------------


@dataclass
class CompoundExpr:
    """Function application or operator: f(arg1, arg2, ...)"""

    func: str
    args: list[Expr]

    def __repr__(self):
        if self.args:
            return f"{self.func}({', '.join(repr(a) for a in self.args)})"
        return self.func


@dataclass
class NameExpr:
    """Variable or constant name."""

    name: str

    def __repr__(self):
        return self.name


@dataclass
class LitExpr:
    """Literal value (int, bool, etc.)"""

    value: str

    def __repr__(self):
        return self.value


Expr = Union[CompoundExpr, NameExpr, LitExpr]


def subterms(expr: Expr) -> list[Expr]:
    """Return all subterms of an expression (including itself), depth-first."""
    result = [expr]
    if isinstance(expr, CompoundExpr):
        for arg in expr.args:
            result.extend(subterms(arg))
    return result


# ---------------------------------------------------------------------------
# Minimal Boogie expression tokenizer + parser
# ---------------------------------------------------------------------------

# Boogie identifiers can contain letters, digits, _, $, #, @, !, ., ?
_TOKEN_RE = re.compile(
    r"(?P<IDENT>[a-zA-Z_$][a-zA-Z0-9_$#@!?.]*(?:\s*:\s*[a-zA-Z_$][a-zA-Z0-9_$#@!?.<>]*)?)"  # ident with optional :Type cast
    r"|(?P<INT>-?\d+)"
    r"|(?P<LPAREN>\()"
    r"|(?P<RPAREN>\))"
    r"|(?P<LBRACKET>\[)"
    r"|(?P<RBRACKET>\])"
    r"|(?P<COMMA>,)"
    r"|(?P<OP>[+\-*/<>=!&|]+)"
    r"|(?P<WS>\s+)"
)


def tokenize(text: str) -> list[tuple[str, str]]:
    """Return list of (kind, value) tokens, skipping whitespace."""
    tokens = []
    for m in _TOKEN_RE.finditer(text):
        kind = m.lastgroup
        if kind == "WS":
            continue
        # Strip type cast suffix from identifiers (e.g. "x: int" → "x")
        val = m.group()
        if kind == "IDENT" and ":" in val:
            val = val[: val.index(":")].strip()
        tokens.append((kind, val))
    return tokens


class _Parser:
    def __init__(self, tokens: list[tuple[str, str]]):
        self._toks = tokens
        self._pos = 0

    def _peek(self) -> Optional[tuple[str, str]]:
        return self._toks[self._pos] if self._pos < len(self._toks) else None

    def _consume(self) -> tuple[str, str]:
        tok = self._toks[self._pos]
        self._pos += 1
        return tok

    def parse(self) -> Optional[Expr]:
        return self._parse_expr()

    def _parse_expr(self) -> Optional[Expr]:
        """Parse a primary expression (function call or atom)."""
        tok = self._peek()
        if tok is None:
            return None

        kind, val = tok

        if kind == "INT":
            self._consume()
            return LitExpr(val)

        if kind == "LPAREN":
            self._consume()
            inner = self._parse_expr()
            # consume RPAREN if present
            if (peek := self._peek()) and peek[0] == "RPAREN":
                self._consume()
            return inner

        if kind == "IDENT":
            self._consume()
            # Check if followed by LPAREN → function application
            if (peek := self._peek()) and peek[0] == "LPAREN":
                self._consume()  # consume LPAREN
                args = []
                while (peek := self._peek()) and peek[0] != "RPAREN":
                    arg = self._parse_expr()
                    if arg is not None:
                        args.append(arg)
                    if (peek := self._peek()) and peek[0] == "COMMA":
                        self._consume()
                if (peek := self._peek()) and peek[0] == "RPAREN":
                    self._consume()  # consume RPAREN
                return CompoundExpr(val, args)
            # Check if followed by LBRACKET → map/array subscript a[i]
            elif (peek := self._peek()) and peek[0] == "LBRACKET":
                self._consume()  # consume LBRACKET
                args = []
                while (peek := self._peek()) and peek[0] != "RBRACKET":
                    arg = self._parse_expr()
                    if arg is not None:
                        args.append(arg)
                    if (peek := self._peek()) and peek[0] == "COMMA":
                        self._consume()
                if (peek := self._peek()) and peek[0] == "RBRACKET":
                    self._consume()  # consume RBRACKET
                return CompoundExpr("$select", [NameExpr(val)] + args)
            else:
                return NameExpr(val)

        if kind == "OP":
            self._consume()
            return NameExpr(val)  # treat stray operators as names

        # Skip unexpected tokens
        self._consume()
        return self._parse_expr()


def parse_expr(text: str) -> Optional[Expr]:
    """Parse a Boogie expression string into an Expr tree. Best-effort."""
    text = text.strip().rstrip(";")
    # Strip outermost parens if present
    if text.startswith("(") and text.endswith(")"):
        text = text[1:-1].strip()
    tokens = tokenize(text)
    if not tokens:
        return None
    return _Parser(tokens).parse()


# ---------------------------------------------------------------------------
# BPL quantifier extractor
# ---------------------------------------------------------------------------


@dataclass
class BplQuantifier:
    """A quantifier extracted from a BPL file."""

    kind: str  # "axiom" or "user"
    bound_vars: list[str]  # names of bound variables
    triggers: list[Expr]  # parsed trigger expressions
    raw_trigger: str  # raw trigger text for debugging
    line: int  # line number in BPL


def _extract_binders(forall_text: str) -> list[str]:
    """Extract bound variable names from 'x1: T1, x2: T2, ...' text."""
    binders = []
    # Split on comma (careful: types can contain angle brackets)
    depth = 0
    current = []
    for ch in forall_text:
        if ch in "<([":
            depth += 1
            current.append(ch)
        elif ch in ">)]":
            depth -= 1
            current.append(ch)
        elif ch == "," and depth == 0:
            binders.append("".join(current).strip())
            current = []
        else:
            current.append(ch)
    if current:
        binders.append("".join(current).strip())

    names = []
    for b in binders:
        # "x: T" or "x1, x2: T" — take name before ":"
        b = b.strip()
        if ":" in b:
            names.append(b[: b.index(":")].strip())
        else:
            names.append(b.strip())
    return [n for n in names if n]


def _split_trigger_terms(inner: str) -> list[str]:
    """Split comma-separated trigger terms respecting parenthesis/bracket depth."""
    terms = []
    depth = 0
    current: list[str] = []
    for ch in inner:
        if ch in "([":
            depth += 1
            current.append(ch)
        elif ch in ")]":
            depth -= 1
            current.append(ch)
        elif ch == "," and depth == 0:
            terms.append("".join(current).strip())
            current = []
        else:
            current.append(ch)
    if current:
        terms.append("".join(current).strip())
    return terms


def _parse_triggers(trigger_block: str) -> list[Expr]:
    """Parse the { e1 }, { e2 } trigger block into a list of Expr."""
    exprs = []
    for m in re.finditer(r"\{([^}]+)\}", trigger_block):
        inner = m.group(1).strip()
        # Skip pure attribute blocks like {:id "..."} or {:weight N}
        if inner.startswith(":"):
            continue
        for term in _split_trigger_terms(inner):
            term = term.strip()
            if not term or term.startswith(":"):
                continue
            e = parse_expr(term)
            if e is not None:
                exprs.append(e)
    return exprs


def extract_quantifiers(bpl_text: str) -> list[BplQuantifier]:
    """
    Extract all quantifiers with trigger patterns from a BPL file.
    Handles both axiom-level and procedure-level (assume) quantifiers.

    Performance note: axiom quantifiers (kind="axiom") are identical across all
    Dafny files compiled with the same Dafny version — they come entirely from
    DafnyPrelude.bpl. If classifying many assertions across many files, consider
    parsing the prelude once and caching those quantifiers. The user quantifiers
    (kind="user") are file-specific and cannot be cached.

    Batching caveat: when classifying multiple assertions from the same file using
    one shared BPL, be aware that an essential assertion of the form
    `assert forall x :: P(x)` compiles to both `assert (forall ...)` and
    `assume (forall ...)` in BPL. The assume is picked up as a user quantifier and
    may create spurious trigger matches for other assertions in the same procedure.
    """
    quantifiers: list[BplQuantifier] = []
    lines = bpl_text.splitlines()

    # Join lines for multi-line quantifier detection
    # We scan for "axiom (forall" and "assume ... (forall" patterns
    i = 0
    while i < len(lines):
        line = lines[i]
        stripped = line.strip()

        is_axiom = stripped.startswith("axiom") and "forall" in stripped
        is_user = re.match(r"\s*assume\b.*forall\b", line) and not stripped.startswith(
            "//"
        )

        if not (is_axiom or is_user):
            i += 1
            continue

        kind = "axiom" if is_axiom else "user"

        # Collect the full quantifier text (multi-line) until we balance parens
        block_lines = []
        depth = 0
        j = i
        while j < len(lines):
            block_lines.append(lines[j])
            depth += lines[j].count("(") - lines[j].count(")")
            j += 1
            if depth <= 0 and len(block_lines) > 0:
                break

        block = " ".join(block_lines)

        # Extract binders: text between "forall" and "::"
        m_binders = re.search(r"forall\s*(<[^>]*>\s*)?(.*?)\s*::", block)
        bound_vars = _extract_binders(m_binders.group(2)) if m_binders else []

        # Extract trigger block: { ... } between :: and the body
        # Everything between "::" and the first non-brace, non-attribute content
        trigger_raw = ""
        m_trigger = re.search(r"::\s*(\s*(?:\{[^}]*\}\s*)+)", block)
        if m_trigger:
            trigger_raw = m_trigger.group(1)

        triggers = _parse_triggers(trigger_raw)

        if triggers:
            quantifiers.append(
                BplQuantifier(
                    kind=kind,
                    bound_vars=bound_vars,
                    triggers=triggers,
                    raw_trigger=trigger_raw.strip(),
                    line=i + 1,
                )
            )

        i = j  # skip past the block we just processed

    return quantifiers


# ---------------------------------------------------------------------------
# Pattern matching
# ---------------------------------------------------------------------------

Substitution = Dict[str, Expr]


def match(expr: Expr, pattern: Expr, bound_vars: set[str], sigma: Substitution) -> bool:
    """
    Try to extend sigma so that pattern[sigma] == expr.
    bound_vars: names that are pattern variables (can match anything).
    Returns True if match succeeds (sigma is updated in-place), False otherwise.
    Sigma is NOT rolled back on failure — callers should pass a copy.
    """
    if isinstance(pattern, NameExpr) and pattern.name in bound_vars:
        # Pattern variable: check consistency or bind
        if pattern.name in sigma:
            return _expr_eq(sigma[pattern.name], expr)
        sigma[pattern.name] = expr
        return True

    if isinstance(pattern, LitExpr):
        return isinstance(expr, LitExpr) and expr.value == pattern.value

    if isinstance(pattern, NameExpr):
        return isinstance(expr, NameExpr) and expr.name == pattern.name

    if isinstance(pattern, CompoundExpr):
        if not isinstance(expr, CompoundExpr):
            return False
        if expr.func != pattern.func:
            return False
        if len(expr.args) != len(pattern.args):
            return False
        for e_arg, p_arg in zip(expr.args, pattern.args):
            if not match(e_arg, p_arg, bound_vars, sigma):
                return False
        return True

    return False


def _expr_eq(a: Expr, b: Expr) -> bool:
    """Structural equality for Expr."""
    if type(a) is not type(b):
        return False
    if isinstance(a, LitExpr):
        return a.value == b.value
    if isinstance(a, NameExpr):
        return a.name == b.name
    if isinstance(a, CompoundExpr):
        return (
            a.func == b.func
            and len(a.args) == len(b.args)
            and all(_expr_eq(x, y) for x, y in zip(a.args, b.args))
        )
    return False


def _trigger_specificity(trigger: Expr, bound_vars: set[str]) -> int:
    """
    Score a trigger pattern by how specific/constrained it is.
    Higher = more specific (preferred).
    Counts the number of non-variable nodes in the pattern.
    """
    if isinstance(trigger, NameExpr):
        return 0 if trigger.name in bound_vars else 1
    if isinstance(trigger, LitExpr):
        return 1
    if isinstance(trigger, CompoundExpr):
        return 1 + sum(_trigger_specificity(a, bound_vars) for a in trigger.args)
    return 0


@dataclass
class TriggerMatch:
    quantifier: BplQuantifier
    trigger: Expr
    matched_subterm: Expr
    subterm_depth: int  # depth of matched subterm in assertion (0 = top-level)
    specificity: int  # higher = more constrained trigger


def find_trigger_matches(
    assertion_expr: Expr,
    quantifiers: list[BplQuantifier],
) -> list[TriggerMatch]:
    """
    Return all trigger matches, sorted best-first by:
      1. Shallowest match in assertion (depth 0 = top-level preferred)
      2. Highest trigger specificity (more non-variable nodes)
    """

    def collect_subterms_with_depth(
        expr: Expr, depth: int = 0
    ) -> list[tuple[Expr, int]]:
        result = [(expr, depth)]
        if isinstance(expr, CompoundExpr):
            for arg in expr.args:
                result.extend(collect_subterms_with_depth(arg, depth + 1))
        return result

    subterms_with_depth = collect_subterms_with_depth(assertion_expr)
    matches: list[TriggerMatch] = []

    for q in quantifiers:
        bound = set(q.bound_vars)
        for trigger in q.triggers:
            spec = _trigger_specificity(trigger, bound)
            # Skip degenerate triggers that are just a bare variable — they
            # match anything and provide no useful information.
            if spec == 0:
                continue
            for sub, depth in subterms_with_depth:
                sigma: Substitution = {}
                if match(sub, trigger, bound, dict(sigma)):
                    matches.append(
                        TriggerMatch(
                            quantifier=q,
                            trigger=trigger,
                            matched_subterm=sub,
                            subterm_depth=depth,
                            specificity=spec,
                        )
                    )
                    break  # one match per (quantifier, trigger) is enough

    # Sort: shallowest depth first, then highest specificity
    matches.sort(key=lambda m: (m.subterm_depth, -m.specificity))
    return matches


def find_trigger_match(
    assertion_expr: Expr,
    quantifiers: list[BplQuantifier],
) -> Optional[TriggerMatch]:
    """Return the best-ranked trigger match, or None."""
    matches = find_trigger_matches(assertion_expr, quantifiers)
    return matches[0] if matches else None


# ---------------------------------------------------------------------------
# BPL generation
# ---------------------------------------------------------------------------


async def generate_bpl_async(
    pool: DafnyPool, dfy_path: Path, timeout: int = 30
) -> tuple[str, str]:
    """
    Run modified Dafny on dfy_path to produce BPL text and ast_mapping JSON.
    Returns (bpl_text, ast_mapping_json_text).
    Raises RuntimeError on failure.
    """
    with tempfile.TemporaryDirectory() as tmpdir:
        bpl_path = Path(tmpdir) / "output.bpl"
        ast_path = Path(tmpdir) / "ast_mapping.json"
        args = CustomDafnyArgs(
            file_path=dfy_path,
            verification_time_limit=timeout,
            bprint_file=bpl_path,
            ast_mapping_file=ast_path,
            timeout_seconds=timeout + 60,
        )
        output = await pool.run_custom_dafny(args)
        if not bpl_path.exists():
            raise RuntimeError(
                f"BPL not generated. Dafny output:\n{output.raw_output[:500]}"
            )
        bpl_text = bpl_path.read_text()
        ast_text = ast_path.read_text() if ast_path.exists() else "{}"
        return bpl_text, ast_text


def generate_bpl(
    dfy_path: Path, timeout: int = 30, max_concurrency: int = 1
) -> tuple[str, str]:
    pool = DafnyPool(max_concurrency=max_concurrency)
    return asyncio.run(generate_bpl_async(pool, dfy_path, timeout))


# ---------------------------------------------------------------------------
# Assertion expression lookup
# ---------------------------------------------------------------------------


def find_assert_expr_in_bpl(bpl_text: str, boogie_id: str) -> Optional[Expr]:
    """
    Find `assert {:id "boogie_id"} EXPR;` in the BPL and parse EXPR.
    Handles multi-line assertions.
    """
    lines = bpl_text.splitlines()
    id_pattern = re.compile(
        r'assert\s+(?:\{[^}]*\}\s*)*\{:id\s+"' + re.escape(boogie_id) + r'"\s*\}(.*)',
        re.IGNORECASE,
    )

    for i, line in enumerate(lines):
        m = id_pattern.search(line)
        if not m:
            continue
        # Collect expression text until semicolon (may span lines)
        expr_text = m.group(1)
        j = i + 1
        while ";" not in expr_text and j < len(lines):
            expr_text += " " + lines[j]
            j += 1
        # Strip trailing semicolon and balanced parens around the whole thing
        expr_text = expr_text.strip().rstrip(";").strip()
        return parse_expr(expr_text)

    return None


# ---------------------------------------------------------------------------
# Main classification entry point
# ---------------------------------------------------------------------------


MatchCategory = Literal["ematching-axiom", "ematching-user", "unknown"]


@dataclass
class EmatchingResult:
    boogie_id: str
    category: MatchCategory
    matched_quantifier: Optional[BplQuantifier] = None
    assertion_expr: Optional[str] = None  # repr of parsed assertion
    note: str = ""


async def classify_assertion_async(
    pool: DafnyPool,
    dfy_path: Path,
    boogie_id: str,
    timeout: int = 30,
    bpl_text: str = "",  # pre-generated BPL (skip Dafny run if provided)
) -> EmatchingResult:
    """
    Classify one essential assertion by whether it fires a quantifier trigger.

    Returns ematching-axiom, ematching-user, or unknown.
    For existential witness detection, call classify_witness() separately.

    dfy_path: the original verified .dfy file (with all assertions present)
    boogie_id: the boogieId of the assertion to classify (e.g. "id92")
    """
    # Generate BPL if not provided
    if not bpl_text:
        bpl_text, _ = await generate_bpl_async(pool, dfy_path, timeout)

    # Parse BPL quantifiers
    quantifiers = extract_quantifiers(bpl_text)

    # Find assertion expression in BPL
    assertion_expr = find_assert_expr_in_bpl(bpl_text, boogie_id)
    if assertion_expr is None:
        return EmatchingResult(
            boogie_id=boogie_id,
            category="unknown",
            note=f'could not find assert with id "{boogie_id}" in BPL',
        )

    # Try to find a matching trigger
    matched = find_trigger_match(assertion_expr, quantifiers)

    if matched is None:
        return EmatchingResult(
            boogie_id=boogie_id,
            category="unknown",
            assertion_expr=repr(assertion_expr),
            note="no trigger pattern matched any subterm of the assertion",
        )

    category = (
        "ematching-axiom" if matched.quantifier.kind == "axiom" else "ematching-user"
    )
    return EmatchingResult(
        boogie_id=boogie_id,
        category=category,
        matched_quantifier=matched.quantifier,
        assertion_expr=repr(assertion_expr),
        note=(
            f"trigger: {matched.trigger!r}  matched subterm: {matched.matched_subterm!r}"
            f"  depth={matched.subterm_depth}  specificity={matched.specificity}"
            f"  (BPL line {matched.quantifier.line})"
        ),
    )


def classify_assertion(
    dfy_path: Path,
    boogie_id: str,
    timeout: int = 30,
    bpl_text: str = "",
    max_concurrency: int = 1,
) -> EmatchingResult:
    pool = DafnyPool(max_concurrency=max_concurrency)
    return asyncio.run(
        classify_assertion_async(
            pool=pool,
            dfy_path=dfy_path,
            boogie_id=boogie_id,
            timeout=timeout,
            bpl_text=bpl_text,
        )
    )


# ---------------------------------------------------------------------------
# CLI
# ---------------------------------------------------------------------------


def _ematching_to_dict(r: EmatchingResult) -> dict:
    d: dict = {
        "boogie_id": r.boogie_id,
        "category": r.category,
        "assertion_expr": r.assertion_expr,
        "note": r.note,
    }
    if r.matched_quantifier:
        q = r.matched_quantifier
        d["matched_quantifier"] = {
            "kind": q.kind,
            "bound_vars": q.bound_vars,
            "raw_trigger": q.raw_trigger,
            "line": q.line,
        }
    return d


if __name__ == "__main__":
    import argparse
    import sys

    from smt_analysis.category_checks.category_witness import (
        classify_witness,
        _witness_to_dict,
    )

    parser = argparse.ArgumentParser(
        description="Classify an essential assertion: e-matching category and witness confidence."
    )
    parser.add_argument("--dfy", required=True, help="Path to verified .dfy file")
    parser.add_argument(
        "--boogie-id", required=True, help="boogieId of the assertion (e.g. id92)"
    )
    parser.add_argument("--timeout", type=int, default=30)
    parser.add_argument(
        "--max-concurrency",
        type=int,
        default=1,
        help="Maximum number of Dafny subprocesses to run concurrently",
    )
    parser.add_argument(
        "--bpl", default="", help="Pre-generated BPL file path (skip Dafny run)"
    )
    args = parser.parse_args()
    pool = DafnyPool(max_concurrency=args.max_concurrency)

    bpl_text = Path(args.bpl).read_text() if args.bpl else ""
    if not bpl_text:
        bpl_text, _ = asyncio.run(
            generate_bpl_async(pool, Path(args.dfy), args.timeout)
        )

    em_result = asyncio.run(
        classify_assertion_async(
            pool=pool,
            dfy_path=Path(args.dfy),
            boogie_id=args.boogie_id,
            timeout=args.timeout,
            bpl_text=bpl_text,
        )
    )

    # Also run witness classification if e-matching returned unknown
    witness_result = None
    if em_result.category == "unknown" and em_result.assertion_expr is not None:
        assertion_expr = find_assert_expr_in_bpl(bpl_text, args.boogie_id)
        if assertion_expr is not None:
            witness_result = classify_witness(assertion_expr, bpl_text, args.boogie_id)

    output = {"ematching": _ematching_to_dict(em_result)}
    if witness_result is not None:
        output["witness"] = _witness_to_dict(witness_result)

    print(json.dumps(output, indent=2))
    sys.exit(0 if em_result.category != "unknown" else 1)  # noqa: S101

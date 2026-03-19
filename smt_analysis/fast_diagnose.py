#!/usr/bin/env python3
"""
Fast deterministic SMT quirk diagnosis pipeline.

For each verified problem:
  1. PARSE   — extract assert statements from method bodies
  2. ABLATE  — remove each assertion, run dafny verify, find essential ones
  3. MODEL   — for essential equality assertions, run Boogie /printModel:1
  4. DIAGNOSE — check if LHS ≠ RHS in the model (axiom gap)
  5. REPORT  — write structured findings

Non-equality assertions are flagged for manual review.

Usage:
    python3 smt_analysis/fast_diagnose.py --names 0000_1013_A
    python3 smt_analysis/fast_diagnose.py --all --workers 5
    python3 smt_analysis/fast_diagnose.py --all --ablate-only --workers 5
"""

import argparse
import json
import os
import re
import subprocess
import sys
import time
from concurrent.futures import ProcessPoolExecutor, as_completed
from pathlib import Path

PROJ_ROOT = Path(__file__).parent.parent.resolve()
DATASET_DIR = PROJ_ROOT / "dataset"
RESULTS_DIR = PROJ_ROOT / "smt_analysis" / "results"
HELPERS_DIR = PROJ_ROOT / "smt_analysis" / "helpers"
DOTNET = os.environ.get("DOTNET8", os.environ.get("DOTNET", "dotnet"))
DAFNY_DLL = PROJ_ROOT / "dafny-source" / "Binaries" / "Dafny.dll"
BOOGIE_PROJ = PROJ_ROOT / "boogie" / "Source" / "BoogieDriver" / "BoogieDriver.csproj"


# ---------------------------------------------------------------------------
# Phase 1: Parse assertions from method bodies
# ---------------------------------------------------------------------------

def generate_ast_mapping(dfy_path: Path, output_dir: Path, timeout: int = 60) -> Path | None:
    """Run dafny verify with --ast-mapping to generate a fresh AST mapping.

    Returns path to ast_mapping.json, or None on failure.
    """
    output_dir.mkdir(parents=True, exist_ok=True)
    ast_path = output_dir / "ast_mapping.json"
    bpl_path = output_dir / "output.bpl"

    try:
        result = subprocess.run(
            [DOTNET, str(DAFNY_DLL), "verify", str(dfy_path),
             "--ast-mapping", str(ast_path),
             "--bprint", str(bpl_path),
             "--verification-time-limit", str(timeout)],
            capture_output=True, text=True, timeout=timeout + 60,
        )
        (output_dir / "dafny_output.txt").write_text(result.stdout + "\n" + result.stderr)
    except subprocess.TimeoutExpired:
        (output_dir / "dafny_output.txt").write_text("TIMEOUT during AST generation\n")
        return None

    if ast_path.exists():
        return ast_path
    return None


def parse_assertions(source_file: Path, ast_path: Path) -> list[dict]:
    """Extract assertions from method bodies using ast_mapping.json.

    Only returns assert statements (no lemma calls, no invariants).
    Only from actual Dafny methods (not lemmas).

    Returns list of {index, line, text, expr, is_equality, boogie_id, method}.
    """
    ast = json.loads(ast_path.read_text())

    assertions = []
    idx = 0

    for method in ast.get("methods", []):
        method_name = method["name"]

        # Only process actual Dafny methods (not lemmas)
        if not _is_method_in_source(source_file, method_name):
            continue

        # Collect assertions only (skip invariants, skip calls)
        for a in method.get("assertions", []):
            text = a["text"]
            line = a.get("location", {}).get("line", 0)
            boogie_id = a.get("boogieId", "")

            is_equality = "==" in text and "!==" not in text and "<==" not in text
            if "<==>" in text:
                is_equality = True

            assertions.append({
                "index": idx,
                "line": line,
                "text": f"assert {text};",
                "expr": text,
                "is_equality": is_equality,
                "boogie_id": boogie_id,
                "method": method_name,
            })
            idx += 1

    return assertions


def _is_method_in_source(dfy_path: Path, method_name: str) -> bool:
    """Check if a name is declared as 'method' (not lemma) in the Dafny source."""
    content = dfy_path.read_text()
    return bool(re.search(rf'\bmethod\s+{re.escape(method_name)}\b', content))




# ---------------------------------------------------------------------------
# Phase 2: Ablation — remove each assertion, check if verification still holds
# ---------------------------------------------------------------------------

def _find_assert_end(lines: list[str], start: int) -> int:
    """Find the end line (inclusive) of an assert statement starting at `start`.

    Handles three forms:
      - ``assert expr;``                (single or multi-line, ends at ``;``)
      - ``assert expr by { ... }``      (ends at matching ``}``)
      - ``assert expr\n  by { ... }``   (``by`` on a following line)
    """
    # Collect the assert expression lines until we hit ';' or 'by {'
    j = start
    while j < len(lines):
        stripped = lines[j].strip()
        if "by {" in stripped or "by{" in stripped:
            # assert ... by { ... } block — find matching close brace
            depth = stripped.count("{") - stripped.count("}")
            j += 1
            while j < len(lines) and depth > 0:
                depth += lines[j].count("{") - lines[j].count("}")
                j += 1
            return j - 1  # inclusive
        if stripped.endswith(";"):
            # Check if next non-blank line starts with 'by'
            k = j + 1
            while k < len(lines) and lines[k].strip() == "":
                k += 1
            if k < len(lines) and lines[k].strip().startswith("by"):
                # The 'by' is on the next line — continue from there
                j = k
                continue
            return j
        j += 1
    return min(j, len(lines) - 1)


def create_without_variant(dfy_path: Path, assertion: dict, output_path: Path):
    """Create a variant of the .dfy file with one assertion removed.

    Uses the AST line number to locate the assertion.  For standalone
    assertions (the only statement on the line), the full line range is
    commented out (including any ``by { ... }`` block).  For inline
    assertions (sharing a line with other code, e.g.
    ``if x { assert false; }``), only the ``assert ...;`` text is excised.
    """
    lines = dfy_path.read_text().split("\n")

    start = assertion["line"] - 1
    if start < 0 or start >= len(lines):
        output_path.write_text("\n".join(lines))
        return

    line = lines[start]
    stripped = line.strip()

    # Check if the assert is the only statement on this line
    if stripped.startswith("assert "):
        # Standalone assert — comment out the full block (including by-block)
        end = _find_assert_end(lines, start)
        for j in range(start, end + 1):
            lines[j] = "    // REMOVED: " + lines[j].strip()
    else:
        # Inline assert — surgically remove just the assert text
        # Build the assert text from the AST expression
        expr = assertion["expr"]
        # Try exact removal of "assert <expr>;" from the line
        for pattern in [f"assert {expr};", f" assert {expr};"]:
            if pattern in line:
                lines[start] = line.replace(pattern, "", 1)
                break
        else:
            # Fallback: try normalized matching
            expr_normalized = re.sub(r'\s+', ' ', expr).strip()
            # Find "assert ...;" on this line using regex
            m = re.search(r'assert\s+' + re.escape(expr_normalized) + r'\s*;', line)
            if m:
                lines[start] = line[:m.start()] + line[m.end():]
            else:
                # Last resort: just comment the whole line
                lines[start] = "    // REMOVED: " + stripped

    output_path.write_text("\n".join(lines))


def run_ablation_single(dfy_path: Path, timeout: int = 30) -> dict:
    """Run dafny verify on a single variant file. Returns result dict."""
    result = subprocess.run(
        ["bash", str(HELPERS_DIR / "run_ablation.sh"), str(dfy_path), str(timeout)],
        capture_output=True,
        text=True,
        timeout=timeout + 30,
    )
    try:
        return json.loads(result.stdout)
    except json.JSONDecodeError:
        return {"result": "error", "exit_code": -1, "errors": [result.stderr[:500]], "time_seconds": 0}


def run_ablation(problem_dir: Path, assertions: list[dict], source_file: Path,
                  timeout: int = 30) -> list[dict]:
    """Run ablation on all assertions. Returns updated assertion list with essentiality."""
    ablation_dir = problem_dir / "ablation"
    ablation_dir.mkdir(exist_ok=True)

    verified = source_file

    results = []
    for a in assertions:
        variant_path = ablation_dir / f"without_{a['index']:02d}.dfy"
        create_without_variant(verified, a, variant_path)

        r = run_ablation_single(variant_path, timeout)

        a["ablation_result"] = r["result"]
        a["ablation_time"] = r.get("time_seconds", 0)
        a["ablation_errors"] = r.get("errors", [])[:3]

        # Parse errors and prover errors are NOT genuine essentiality signals —
        # they indicate a bug in assertion removal, not that the solver needs it.
        errs_text = " ".join(a["ablation_errors"])
        if r["result"] == "parse_error" or "parse errors detected" in errs_text:
            a["essential"] = False
            a["ablation_result"] = "parse_error"
            print(f"    [{a['index']:2d}] PARSE_ERROR (removal broke syntax) {a['text'][:60]}")
        elif r["result"] == "prover_error":
            a["essential"] = False
            a["ablation_result"] = "prover_error"
            print(f"    [{a['index']:2d}] PROVER_ERROR (solver crash) {a['text'][:60]}")
        else:
            a["essential"] = r["result"] != "pass"

        if a["essential"]:
            print(f"    [{a['index']:2d}] ESSENTIAL ({r['result']:7s} {r.get('time_seconds', 0):5.1f}s) {a['text'][:70]}")

        results.append(a)

    return results


# ---------------------------------------------------------------------------
# Phase 3: Model extraction — run Boogie /printModel:1 on failing BPL
# ---------------------------------------------------------------------------

def get_model_for_assertion(problem_dir: Path, assertion: dict, timeout: int = 60) -> dict | None:
    """Run full pipeline on without-variant, then Boogie /printModel:1.

    Returns parsed model dict or None on failure.
    """
    variant_path = problem_dir / "ablation" / f"without_{assertion['index']:02d}.dfy"
    if not variant_path.exists():
        return None

    model_dir = problem_dir / "models" / f"assert_{assertion['index']:02d}"
    model_dir.mkdir(parents=True, exist_ok=True)

    # Step 1: Run Dafny to get BPL
    bpl_path = model_dir / "output.bpl"
    dafny_result = subprocess.run(
        [DOTNET, str(DAFNY_DLL), "verify", str(variant_path),
         "--bprint", str(bpl_path),
         "--verification-time-limit", str(timeout)],
        capture_output=True, text=True, timeout=timeout + 60,
    )
    (model_dir / "dafny_output.txt").write_text(dafny_result.stdout + "\n" + dafny_result.stderr)

    if not bpl_path.exists():
        return None

    # Step 2: Run Boogie with /printModel:1
    boogie_result = subprocess.run(
        [DOTNET, "run", "--project", str(BOOGIE_PROJ), "--",
         str(bpl_path), "/printModel:1", f"/timeLimit:{timeout}"],
        capture_output=True, text=True, timeout=timeout + 60,
    )
    raw_model = boogie_result.stdout
    (model_dir / "boogie_model.txt").write_text(raw_model)

    # Step 3: Parse the model
    return parse_boogie_model(raw_model)


def parse_boogie_model(raw: str) -> dict:
    """Parse Boogie's /printModel:1 output into a structured dict.

    Extracts:
      - functions: {name: {(args...): result, "else": default}}
      - states: [{name, bindings: {var: value}}]
    """
    model = {"functions": {}, "states": [], "raw_lines": []}

    lines = raw.split("\n")
    i = 0
    in_model = False

    while i < len(lines):
        line = lines[i]

        # Detect start of function definition: "funcname -> {"
        m = re.match(r'^(\S+)\s+->\s+\{$', line)
        if m:
            fname = m.group(1)
            entries = {}
            i += 1
            while i < len(lines):
                fline = lines[i].strip()
                if fline == "}":
                    break
                # "arg1 arg2 -> result"
                fm = re.match(r'^(.*?)\s+->\s+(.+)$', fline)
                if fm:
                    args = fm.group(1).strip()
                    result = fm.group(2).strip()
                    entries[args] = result
                elif fline and fline != "else ->":
                    # Single value = else case
                    entries["else"] = fline
                i += 1
            model["functions"][fname] = entries
            i += 1
            continue

        # Detect simple constant: "name -> value"
        m = re.match(r'^(\S+)\s+->\s+(.+)$', line)
        if m and "{" not in m.group(2):
            name = m.group(1)
            value = m.group(2).strip()
            if not name.startswith("***") and not name.startswith("aux$$"):
                model["functions"][name] = {"else": value}
            i += 1
            continue

        # Detect state: "*** STATE name"
        m = re.match(r'^\*\*\* STATE (.+)$', line)
        if m:
            state_name = m.group(1)
            bindings = {}
            i += 1
            while i < len(lines):
                sline = lines[i].strip()
                if sline.startswith("*** END_STATE"):
                    break
                sm = re.match(r'^(\S+)\s+->\s+(.*)$', sline)
                if sm:
                    bindings[sm.group(1)] = sm.group(2).strip()
                i += 1
            model["states"].append({"name": state_name, "bindings": bindings})
            i += 1
            continue

        i += 1

    return model


# ---------------------------------------------------------------------------
# Phase 4: Diagnose — heuristic for equality assertions
# ---------------------------------------------------------------------------

# Taxonomy categories (paper: A=E-matching, B=Missing axioms, C=Theory, D=Propagation)
#
# B1: Sequence extensionality — missing object-level equality axioms
SEQ_EXT_PATTERNS = [
    {
        "name": "B1-take-append",
        "high_level": "B-missing-axioms",
        "low_level": "B1-seq-extensionality",
        "sub_pattern": "take-append",
        "desc": "Seq#Take(s, i+1) == Seq#Append(Seq#Take(s, i), Seq#Build(Seq#Index(s, i)))",
        "regex": r'(\w+)\[\.\.(\w+)\s*\+\s*1\]\s*==\s*\1\[\.\.\2\]\s*\+\s*\[\1\[\2\]\]',
    },
    {
        "name": "B1-take-full-length",
        "high_level": "B-missing-axioms",
        "low_level": "B1-seq-extensionality",
        "sub_pattern": "take-full",
        "desc": "Seq#Take(s, |s|) == s",
        "regex": r'(\w+)\[\.\.\|(\1)\|\]\s*==\s*\1',
    },
    {
        "name": "B1-take-of-append-prefix",
        "high_level": "B-missing-axioms",
        "low_level": "B1-seq-extensionality",
        "sub_pattern": "take-of-take",
        "desc": "(a + b)[..|a|] == a  or  combined[..|combined|-1] == a",
        "regex": r'(\w+)\[\.\.\|.*\|\s*-?\s*1?\]\s*==',
    },
    {
        "name": "B1-cons-decomposition",
        "high_level": "B-missing-axioms",
        "low_level": "B1-seq-extensionality",
        "sub_pattern": "cons-decomposition",
        "desc": "s == [s[0]] + s[1..]",
        "regex": r'(\w+)\s*==\s*\[\1\[0\]\]\s*\+\s*\1\[1\.\.\]',
    },
    {
        "name": "B1-slice-index-equiv",
        "high_level": "B-missing-axioms",
        "low_level": "B1-seq-extensionality",
        "sub_pattern": "slice-index-equiv",
        "desc": "a[1..][i] == a[i+1] or similar slice-index equivalence",
        "regex": r'\w+\[\d+\.\.\]\[.*\]\s*==\s*\w+\[',
    },
]

# All patterns for classify_assertion
PATTERNS = SEQ_EXT_PATTERNS


def classify_assertion(assertion: dict, model: dict | None) -> dict:
    """Classify an essential assertion using the 4-category taxonomy.

    Categories:
      A. E-matching gaps (A1-A5): missing witnesses, predicate/function
         instantiation, quantifier instantiation, length tracking
      B. Missing axioms (B1): sequence extensionality
      C. Theory incompleteness (C1): nonlinear arithmetic
      D. Propagation failures (D1-D4): equality, bounds, indexing, case exhaustiveness

    Returns diagnosis dict with {category, high_level, low_level, pattern,
    confidence, details}.
    Always tries both pattern matching and model-based diagnosis when a model
    is available, so we can report both pieces of evidence.
    """
    expr = assertion["expr"]

    # Non-equality → flag (may be A1 existential witness, A2 predicate, etc.)
    if not assertion["is_equality"]:
        return {
            "category": "flagged",
            "high_level": "unknown",
            "low_level": "unknown",
            "reason": "non-equality assertion (may be A1-A5 or D1-D4)",
            "confidence": "n/a",
        }

    result = {}

    # Try known sequence extensionality patterns (B1)
    for pat in PATTERNS:
        if re.search(pat["regex"], expr):
            result = {
                "category": pat["name"],
                "high_level": pat["high_level"],
                "low_level": pat["low_level"],
                "sub_pattern": pat.get("sub_pattern", ""),
                "pattern": pat["desc"],
                "confidence": "high",
                "match": "pattern",
            }
            break

    # Always try model-based diagnosis when model available
    model_diagnosis = None
    if model:
        model_diagnosis = diagnose_from_model(assertion, model)

    if model_diagnosis:
        if result:
            # Pattern matched AND model confirmed — attach model evidence
            result["model_evidence"] = model_diagnosis.get("details", {})
            result["model_confirms"] = model_diagnosis["category"]
        else:
            # No pattern match, use model diagnosis
            result = model_diagnosis
    elif not result:
        # No pattern, no model evidence
        result = {
            "category": "unknown-equality",
            "high_level": "unknown",
            "low_level": "unknown",
            "reason": "no pattern match" + (", model inconclusive" if model else ", no model"),
            "confidence": "low",
            "expr": expr,
        }

    return result


def diagnose_from_model(assertion: dict, model: dict) -> dict | None:
    """Try to diagnose an equality assertion from the Boogie model.

    For `assert LHS == RHS`, check if Seq operations on LHS and RHS
    map to different abstract values in the model.
    """
    expr = assertion["expr"]

    # Split on == (handle <==> too)
    if "<==>" in expr:
        parts = expr.split("<==>", 1)
    else:
        # Split on == but not !== or <== or ==>
        parts = re.split(r'(?<!=)(?<!<)==(?!=)', expr, maxsplit=1)

    if len(parts) != 2:
        return None

    lhs = parts[0].strip()
    rhs = parts[1].strip()

    # Look for sequence operations in the model
    seq_funcs = {}
    for fname, entries in model.get("functions", {}).items():
        if fname.startswith("Seq#") or fname.startswith("_module."):
            seq_funcs[fname] = entries

    if not seq_funcs:
        return None

    # Gather info about what sequence terms exist in the model
    seq_take = model["functions"].get("Seq#Take", {})
    seq_append = model["functions"].get("Seq#Append", {})
    seq_build = model["functions"].get("Seq#Build", {})
    seq_length = model["functions"].get("Seq#Length", {})

    # Report what we found in the model
    details = {
        "lhs": lhs,
        "rhs": rhs,
        "seq_take_entries": len(seq_take),
        "seq_append_entries": len(seq_append),
        "seq_length_entries": len(seq_length),
    }

    # Check for the classic pattern: two sequences with same length but different identity
    # Find all seq values and their lengths
    seq_lengths = {}
    for args, result in seq_length.items():
        if args != "else":
            seq_lengths[args] = result

    # Find sequences that have the same length but are different objects
    # This is suggestive of an equality gap
    by_length = {}
    for seq_val, length in seq_lengths.items():
        by_length.setdefault(length, []).append(seq_val)

    suspicious_pairs = {}
    for length, seqs in by_length.items():
        if len(seqs) > 1:
            suspicious_pairs[length] = seqs

    if suspicious_pairs:
        details["suspicious_same_length_seqs"] = suspicious_pairs

        # Check if any of these pairs are related via Seq#Take/Seq#Append
        for length, seqs in suspicious_pairs.items():
            take_produces = set()
            append_produces = set()
            for args, result in seq_take.items():
                if args != "else" and result in seqs:
                    take_produces.add(result)
            for args, result in seq_append.items():
                if args != "else" and result in seqs:
                    append_produces.add(result)

            if take_produces and append_produces and take_produces != append_produces:
                details["axiom_gap"] = {
                    "take_produces": list(take_produces),
                    "append_produces": list(append_produces),
                    "missing_equality": f"Seq#Take result ({list(take_produces)}) ≠ Seq#Append result ({list(append_produces)}) despite same length ({length})",
                }
                return {
                    "category": "B1-seq-extensionality",
                    "high_level": "B-missing-axioms",
                    "low_level": "B1-seq-extensionality",
                    "confidence": "high",
                    "match": "model",
                    "details": details,
                }

    # If we found seq operations but couldn't pinpoint the gap
    if seq_funcs:
        return {
            "category": "unknown-equality-with-model",
            "high_level": "unknown",
            "low_level": "unknown",
            "confidence": "medium",
            "match": "model-inconclusive",
            "details": details,
        }

    return None


# ---------------------------------------------------------------------------
# Phase 5: Report
# ---------------------------------------------------------------------------

def process_problem(problem_name: str, ablate_only: bool = False,
                    model_timeout: int = 60, ablation_timeout: int = 30) -> dict:
    """Run the full pipeline on one problem. Returns report dict."""
    problem_dir = RESULTS_DIR / problem_name

    # Pick source file: inlined > verified
    # But only use inlined if it's valid (has a method declaration)
    source_file = problem_dir / "verified_inlined.dfy"
    if source_file.exists():
        content = source_file.read_text()
        if not re.search(r'\bmethod\s+\w+', content):
            print(f"  Warning: {source_file.name} has no method declaration, using verified.dfy")
            source_file = problem_dir / "verified.dfy"
    else:
        source_file = problem_dir / "verified.dfy"
    if not source_file.exists():
        return {"problem": problem_name, "error": "no verified.dfy"}

    print(f"\n{'='*60}")
    print(f"Processing: {problem_name}")
    print(f"{'='*60}")

    t0 = time.time()

    # Phase 0: Generate fresh AST mapping from the source file
    artifacts_dir = problem_dir / "artifacts"
    print(f"\n  Phase 0: Generating AST mapping from {source_file.name}...")
    ast_path = generate_ast_mapping(source_file, artifacts_dir, timeout=ablation_timeout)
    if not ast_path:
        return {"problem": problem_name, "error": "AST generation failed"}

    # Phase 1: Parse assertions (only assert statements in method bodies)
    print(f"  Phase 1: Parsing assertions...")
    assertions = parse_assertions(source_file, ast_path)
    n_eq = sum(1 for a in assertions if a["is_equality"])
    print(f"    Found {len(assertions)} assertions ({n_eq} equality)")

    if not assertions:
        report = {
            "problem": problem_name,
            "total_assertions": 0,
            "essential": [],
            "non_essential": [],
            "diagnoses": [],
            "elapsed": 0,
        }
        (problem_dir / "fast_report.json").write_text(json.dumps(report, indent=2))
        return report

    # Phase 2: Ablate — find which assertions are essential
    print(f"\n  Phase 2: Ablating {len(assertions)} assertions...")
    assertions = run_ablation(problem_dir, assertions, source_file, timeout=ablation_timeout)

    # Only keep essential assertions from here on
    essential = [a for a in assertions if a["essential"]]
    non_essential = [a for a in assertions if not a["essential"]]
    print(f"\n    Essential: {len(essential)}, Non-essential: {len(non_essential)}")

    # Save ablation results
    ablation_results = {
        "total": len(assertions),
        "essential_count": len(essential),
        "results": assertions,
    }
    ablation_dir = problem_dir / "ablation"
    ablation_dir.mkdir(exist_ok=True)
    (ablation_dir / "results.json").write_text(json.dumps(ablation_results, indent=2, default=str))

    if ablate_only:
        report = {
            "problem": problem_name,
            "total_assertions": len(assertions),
            "essential_count": len(essential),
            "essential": [{"line": a["line"], "text": a["text"], "is_equality": a["is_equality"]}
                          for a in essential],
            "non_essential_count": len(non_essential),
            "elapsed": round(time.time() - t0, 1),
        }
        (problem_dir / "fast_report.json").write_text(json.dumps(report, indent=2))
        return report

    # Phase 3+4: Model + Diagnose (only for essential assertions)
    diagnoses = []
    for a in essential:
        print(f"\n  Diagnosing assertion {a['index']}: {a['text'][:60]}...")

        model = None
        if a["is_equality"] and not a.get("is_lemma_call"):
            # Try model extraction for equality assertions
            try:
                model = get_model_for_assertion(problem_dir, a, timeout=model_timeout)
            except Exception as e:
                print(f"    Model extraction failed: {e}")

        diagnosis = classify_assertion(a, model)
        diagnosis["assertion"] = a["text"]
        diagnosis["line"] = a["line"]
        diagnosis["index"] = a["index"]
        diagnoses.append(diagnosis)

        cat = diagnosis["category"]
        conf = diagnosis.get("confidence", "?")
        print(f"    → {cat} (confidence: {conf})")

    elapsed = round(time.time() - t0, 1)

    # Build report
    report = {
        "problem": problem_name,
        "total_assertions": len(assertions),
        "essential_count": len(essential),
        "non_essential_count": len(non_essential),
        "diagnoses": diagnoses,
        "summary": {
            "by_category": {},
        },
        "elapsed": elapsed,
    }

    # Summarize by category
    for d in diagnoses:
        cat = d["category"]
        report["summary"]["by_category"].setdefault(cat, 0)
        report["summary"]["by_category"][cat] += 1

    (problem_dir / "fast_report.json").write_text(json.dumps(report, indent=2, default=str))
    print(f"\n  Done in {elapsed}s. Report: {problem_dir / 'fast_report.json'}")

    return report


def diagnose_problem(problem_name: str, model_timeout: int = 60) -> dict:
    """Run diagnosis on existing ablation results. No re-ablation."""
    problem_dir = RESULTS_DIR / problem_name
    ablation_path = problem_dir / "ablation" / "results.json"
    if not ablation_path.exists():
        return {"problem": problem_name, "error": "no ablation results"}

    print(f"\n{'='*60}")
    print(f"Diagnosing: {problem_name}")
    print(f"{'='*60}")

    t0 = time.time()
    ablation = json.loads(ablation_path.read_text())
    assertions = ablation.get("results", [])
    essential = [a for a in assertions if a.get("essential")]

    if not essential:
        report = {
            "problem": problem_name,
            "total_assertions": len(assertions),
            "essential_count": 0,
            "non_essential_count": len(assertions),
            "diagnoses": [],
            "elapsed": 0,
        }
        (problem_dir / "fast_report.json").write_text(json.dumps(report, indent=2))
        return report

    print(f"  {len(essential)} essential assertions ({sum(1 for a in essential if a.get('is_equality'))} equality)")

    diagnoses = []
    for a in essential:
        print(f"  Diagnosing [{a.get('index', '?')}]: {a.get('text', '')[:60]}...")

        model = None
        if a.get("is_equality"):
            try:
                model = get_model_for_assertion(problem_dir, a, timeout=model_timeout)
                if model:
                    nfunc = len(model.get("functions", {}))
                    nstate = len(model.get("states", []))
                    print(f"    Model: {nfunc} functions, {nstate} states")
                else:
                    print(f"    No model extracted")
            except subprocess.TimeoutExpired:
                print(f"    Model extraction timed out")
            except Exception as e:
                print(f"    Model extraction failed: {e}")

        diagnosis = classify_assertion(a, model)
        diagnosis["assertion"] = a.get("text", "")
        diagnosis["line"] = a.get("line", 0)
        diagnosis["index"] = a.get("index", 0)
        diagnoses.append(diagnosis)

        cat = diagnosis["category"]
        conf = diagnosis.get("confidence", "?")
        print(f"    -> {cat} (confidence: {conf})")

    elapsed = round(time.time() - t0, 1)

    report = {
        "problem": problem_name,
        "total_assertions": len(assertions),
        "essential_count": len(essential),
        "non_essential_count": len(assertions) - len(essential),
        "diagnoses": diagnoses,
        "summary": {"by_category": {}},
        "elapsed": elapsed,
    }
    for d in diagnoses:
        cat = d["category"]
        report["summary"]["by_category"].setdefault(cat, 0)
        report["summary"]["by_category"][cat] += 1

    (problem_dir / "fast_report.json").write_text(json.dumps(report, indent=2, default=str))
    print(f"  Done in {elapsed}s")
    return report


# ---------------------------------------------------------------------------
# Orchestrator
# ---------------------------------------------------------------------------

def get_verified_problems() -> list[str]:
    """Get problem names that actually verify (from verified_problems.txt).

    Falls back to all directories with verified.dfy if the list doesn't exist.
    """
    verified_list = RESULTS_DIR / "verified_problems.txt"
    if verified_list.exists():
        return sorted(verified_list.read_text().split())
    names = []
    for d in sorted(RESULTS_DIR.iterdir()):
        if d.is_dir() and (d / "verified.dfy").exists():
            names.append(d.name)
    return names


def main():
    parser = argparse.ArgumentParser(description="Fast deterministic SMT quirk diagnosis")
    group = parser.add_mutually_exclusive_group(required=True)
    group.add_argument("--names", type=str, nargs="+", help="Problem names")
    group.add_argument("--all", action="store_true", help="All verified problems")
    parser.add_argument("--workers", type=int, default=1, help="Parallel workers (default: 1)")
    parser.add_argument("--ablate-only", action="store_true", help="Only run ablation, skip model/diagnosis")
    parser.add_argument("--diagnose-only", action="store_true", help="Only run diagnosis on existing ablation results")
    parser.add_argument("--skip-done", action="store_true", help="Skip problems with existing fast_report.json")
    parser.add_argument("--ablation-timeout", type=int, default=30, help="Timeout per ablation run (default: 30s)")
    parser.add_argument("--model-timeout", type=int, default=60, help="Timeout for model extraction (default: 60s)")

    args = parser.parse_args()

    if args.all:
        names = get_verified_problems()
    else:
        names = args.names

    if args.diagnose_only:
        # Filter to problems with existing ablation results that have essential assertions
        names = [n for n in names
                 if (RESULTS_DIR / n / "ablation" / "results.json").exists()]
        # Further filter: only problems that have essential assertions
        filtered = []
        for n in names:
            ablation = json.loads((RESULTS_DIR / n / "ablation" / "results.json").read_text())
            if any(a.get("essential") for a in ablation.get("results", [])):
                filtered.append(n)
        names = filtered
        print(f"Diagnosing {len(names)} problems with essential assertions (workers={args.workers})")
    else:
        if args.skip_done:
            before = len(names)
            names = [n for n in names if not (RESULTS_DIR / n / "fast_report.json").exists()]
            skipped = before - len(names)
            if skipped:
                print(f"Skipping {skipped} already-diagnosed problems")
        print(f"Processing {len(names)} problems (workers={args.workers}, ablate_only={args.ablate_only})")

    t0 = time.time()
    all_reports = []

    if args.diagnose_only:
        if args.workers == 1:
            for name in names:
                r = diagnose_problem(name, model_timeout=args.model_timeout)
                all_reports.append(r)
        else:
            with ProcessPoolExecutor(max_workers=args.workers) as executor:
                futures = {
                    executor.submit(diagnose_problem, name, args.model_timeout): name
                    for name in names
                }
                for future in as_completed(futures):
                    try:
                        r = future.result()
                        all_reports.append(r)
                    except Exception as e:
                        name = futures[future]
                        print(f"  ERROR on {name}: {e}")
                        all_reports.append({"problem": name, "error": str(e)})
    elif args.workers == 1:
        for name in names:
            r = process_problem(name, ablate_only=args.ablate_only,
                                model_timeout=args.model_timeout,
                                ablation_timeout=args.ablation_timeout)
            all_reports.append(r)
    else:
        with ProcessPoolExecutor(max_workers=args.workers) as executor:
            futures = {
                executor.submit(process_problem, name, args.ablate_only,
                                args.model_timeout, args.ablation_timeout): name
                for name in names
            }
            for future in as_completed(futures):
                try:
                    r = future.result()
                    all_reports.append(r)
                except Exception as e:
                    name = futures[future]
                    print(f"  ERROR on {name}: {e}")
                    all_reports.append({"problem": name, "error": str(e)})

    elapsed = round(time.time() - t0, 1)

    # Overall summary
    print(f"\n{'='*60}")
    print(f"OVERALL SUMMARY ({elapsed}s)")
    print(f"{'='*60}")

    total_essential = sum(r.get("essential_count", 0) for r in all_reports)
    total_assertions = sum(r.get("total_assertions", 0) for r in all_reports)

    if not args.ablate_only:
        all_diagnoses = []
        for r in all_reports:
            for d in r.get("diagnoses", []):
                d["problem"] = r["problem"]
                all_diagnoses.append(d)

        by_cat = {}
        for d in all_diagnoses:
            cat = d["category"]
            by_cat.setdefault(cat, []).append(d)

        print(f"Problems: {len(all_reports)}")
        print(f"Total assertions: {total_assertions}, Essential: {total_essential}")
        print(f"\nDiagnosis categories:")
        for cat, items in sorted(by_cat.items(), key=lambda x: -len(x[1])):
            print(f"  {cat}: {len(items)}")
            for item in items[:3]:
                print(f"    - [{item['problem']}:{item.get('line','')}] {item.get('assertion','')[:60]}")

        # Save global summary
        summary = {
            "total_problems": len(all_reports),
            "total_assertions": total_assertions,
            "total_essential": total_essential,
            "by_category": {cat: len(items) for cat, items in by_cat.items()},
            "all_diagnoses": all_diagnoses,
            "elapsed": elapsed,
        }
        (RESULTS_DIR / "diagnosis_summary.json").write_text(json.dumps(summary, indent=2, default=str))
        print(f"\nSummary: {RESULTS_DIR / 'diagnosis_summary.json'}")
    else:
        print(f"Problems: {len(all_reports)}")
        print(f"Total assertions: {total_assertions}, Essential: {total_essential}")


if __name__ == "__main__":
    main()

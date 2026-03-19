#!/usr/bin/env python3
"""
Ablation + Diagnosis pipeline for a verified Dafny problem.

Given a verified.dfy (with assertions added by the LLM):
1. Extract all `assert` statements from verified.dfy
2. Remove each one individually, run `dafny verify` (ablation)
3. For each essential assertion (removal kills the proof):
   a. Run full logging (run_dafny_verify.sh) on the without-assertion variant
   b. Run annotate.py on BOTH (with and without) to get annotated logs
   c. Compare the annotated logs — which VCs fail, what differs
   d. Extract SMT evidence — which axioms/triggers are relevant, what's missing
4. Produce a structured diagnosis with clear evidence chain

Usage:
    python3 smt_analysis/ablate_and_diagnose.py <problem_dir>

    where <problem_dir> has:
      - artifacts/verified.dfy
      - artifacts/annotated_log.json
      - artifacts/output.bpl, name_map.json, ast_mapping.json, output.smt2, dafny_output.txt
"""

import argparse
import json
import re
import subprocess
import sys
import time
from pathlib import Path

PROJ_ROOT = Path(__file__).parent.parent.resolve()
ABLATION_SH = PROJ_ROOT / "smt_analysis" / "helpers" / "run_ablation.sh"
VERIFY_SH = PROJ_ROOT / "smt_analysis" / "helpers" / "run_dafny_verify.sh"
ANNOTATE_PY = PROJ_ROOT / "smt_analysis" / "annotate.py"

# Dafny → SMT operation mapping
DAFNY_TO_SMT_OPS = {
    "[..": "Seq#Take",
    "..]": "Seq#Drop",
    "+ [": "Seq#Append,Seq#Build",
    "== [": "Seq#Equal",
    "] + ": "Seq#Append",
    "[0]": "Seq#Index",
    "[1..]": "Seq#Drop",
    "|": "Seq#Length",
}


# ═══════════════════════════════════════════════════════════════════════════
# Ablation — find essential assertions
# ═══════════════════════════════════════════════════════════════════════════


def extract_asserts(dfy_path: Path) -> list[dict]:
    """Extract all assert statements from a Dafny file.

    Handles both single-line asserts (``assert expr;``) and multi-line
    ``assert expr by { ... }`` blocks.  Returns a list of top-level assert
    blocks — inner assertions nested inside a ``by`` block are *not* included
    as separate entries.
    """
    lines = dfy_path.read_text().splitlines()
    blocks: list[dict] = []
    i = 0
    while i < len(lines):
        stripped = lines[i].strip()
        if stripped.startswith("assert "):
            start = i
            if "by {" in stripped:
                # Find matching closing brace
                depth = stripped.count("{") - stripped.count("}")
                j = i + 1
                while j < len(lines) and depth > 0:
                    depth += lines[j].count("{") - lines[j].count("}")
                    j += 1
                end = j - 1  # inclusive
            elif stripped.endswith(";"):
                end = i
            else:
                # Multi-line assert without by
                j = i + 1
                while j < len(lines) and not lines[j].strip().endswith(";"):
                    j += 1
                end = j
            text = " ".join(lines[k].strip() for k in range(start, end + 1))
            blocks.append({
                "index": len(blocks),
                "line": start + 1,   # 1-indexed
                "line_idx": start,    # 0-indexed start
                "end_idx": end,       # 0-indexed end (inclusive)
                "text": text,
            })
        i += 1

    # Filter out asserts nested inside another assert's by-block
    toplevel = []
    for b in blocks:
        inside = any(
            o["line_idx"] < b["line_idx"] and b["end_idx"] <= o["end_idx"]
            for o in blocks if o is not b
        )
        if not inside:
            toplevel.append(b)
    # Re-index
    for idx, b in enumerate(toplevel):
        b["index"] = idx
    return toplevel


def create_variant(dfy_path: Path, assert_info: dict, output_path: Path):
    """Create a variant with one assert removed (entire block for by-blocks)."""
    lines = dfy_path.read_text().splitlines(keepends=True)
    start = assert_info["line_idx"]
    end = assert_info.get("end_idx", start)
    for idx in range(start, end + 1):
        lines[idx] = f"// REMOVED: {lines[idx]}"
    output_path.write_text("".join(lines))


def run_ablation(variant_path: Path, timeout: int = 30) -> dict:
    """Run quick ablation check on a variant."""
    result = subprocess.run(
        ["bash", str(ABLATION_SH), str(variant_path), str(timeout)],
        capture_output=True, text=True, timeout=timeout + 30,
    )
    try:
        return json.loads(result.stdout)
    except json.JSONDecodeError:
        return {"result": "parse_error", "raw_output": result.stdout}


# ═══════════════════════════════════════════════════════════════════════════
# Full logging + annotation
# ═══════════════════════════════════════════════════════════════════════════


def run_full_logging(dfy_path: Path, output_dir: Path, timeout: int = 60):
    """Run full dafny verify with SMT logging."""
    output_dir.mkdir(parents=True, exist_ok=True)
    subprocess.run(
        ["bash", str(VERIFY_SH), str(dfy_path), str(output_dir), str(timeout)],
        capture_output=True, text=True, timeout=timeout + 60,
    )


def run_annotate(artifacts_dir: Path, output_path: Path):
    """Run annotate.py on a set of artifacts."""
    bpl = artifacts_dir / "output.bpl"
    name_map = artifacts_dir / "name_map.json"
    ast_mapping = artifacts_dir / "ast_mapping.json"
    smt = artifacts_dir / "output.smt2"
    dafny_out = artifacts_dir / "dafny_output.txt"

    if not name_map.exists() or not ast_mapping.exists():
        return None

    cmd = [
        sys.executable, str(ANNOTATE_PY),
        "--name-map", str(name_map),
        "--ast-mapping", str(ast_mapping),
    ]
    if bpl.exists():
        cmd.extend(["--bpl", str(bpl)])
    if smt.exists():
        cmd.extend(["--smt", str(smt)])
    if dafny_out.exists():
        cmd.extend(["--dafny-output", str(dafny_out)])
    cmd.extend(["-o", str(output_path)])

    subprocess.run(cmd, capture_output=True, text=True, timeout=120)
    if output_path.exists():
        return json.loads(output_path.read_text())
    return None


def compare_annotations(with_ann: dict, without_ann: dict) -> dict:
    """Compare two annotated logs to find what changed."""
    diff = {
        "verification_result_change": {
            "with": with_ann.get("summary", {}).get("verification_result", ""),
            "without": without_ann.get("summary", {}).get("verification_result", ""),
        },
        "new_errors": without_ann.get("dafny_errors", []),
        "vc_diffs": [],
    }

    with_vcs = {vc["vc_id"]: vc for vc in with_ann.get("vcs", [])}
    without_vcs = {vc["vc_id"]: vc for vc in without_ann.get("vcs", [])}

    for vc_id in set(list(with_vcs.keys()) + list(without_vcs.keys())):
        w = with_vcs.get(vc_id)
        wo = without_vcs.get(vc_id)
        if not (w and wo):
            continue

        w_flags = set(w.get("assertion_flags", {}).keys())
        wo_flags = set(wo.get("assertion_flags", {}).keys())
        removed_flags = w_flags - wo_flags
        added_flags = wo_flags - w_flags

        w_counts = w.get("assertion_type_counts", {})
        wo_counts = wo.get("assertion_type_counts", {})

        if removed_flags or added_flags or w_counts != wo_counts:
            vc_diff = {
                "vc_id": vc_id,
                "purpose": w.get("purpose", ""),
                "flags_removed": list(removed_flags),
                "flags_added": list(added_flags),
                "type_counts_with": w_counts,
                "type_counts_without": wo_counts,
            }
            if removed_flags:
                vc_diff["removed_flag_details"] = {
                    f: w["assertion_flags"][f]
                    for f in removed_flags
                    if f in w.get("assertion_flags", {})
                }
            diff["vc_diffs"].append(vc_diff)

    return diff


# ═══════════════════════════════════════════════════════════════════════════
# SMT Evidence Extraction — the core diagnostic
# ═══════════════════════════════════════════════════════════════════════════


def extract_smt_evidence(
    assert_info: dict,
    artifacts_dir: Path,
    with_annotation: dict | None,
) -> dict:
    """Extract concrete SMT-level evidence for why an assertion is needed.

    Reads the SMT preamble and name_map to:
    1. Identify which SMT operations the assertion involves
    2. Find all relevant axioms and their trigger patterns
    3. Determine which axiom/trigger is missing (the gap)
    """
    evidence = {
        "smt_encoding": {},
        "relevant_axioms": [],
        "trigger_gap": None,
    }

    smt_path = artifacts_dir / "output.smt2"
    name_map_path = artifacts_dir / "name_map.json"
    if not smt_path.exists() or not name_map_path.exists():
        return evidence

    with open(name_map_path) as f:
        name_map = json.load(f)
    gv = name_map.get("variables", {})

    # Build reverse map: Boogie name → SMT name
    boogie_to_smt = {v: k for k, v in gv.items()}

    # Identify which Seq/Set operations are in the assertion
    assert_text = assert_info["text"]
    smt_ops = _identify_smt_operations(assert_text)
    evidence["smt_encoding"]["dafny"] = assert_text
    evidence["smt_encoding"]["operations"] = smt_ops

    # Translate the assertion to SMT terms
    smt_terms = _dafny_assert_to_smt_terms(assert_text, gv)
    evidence["smt_encoding"]["smt_terms"] = smt_terms

    # Read the SMT preamble to find relevant axioms
    with open(smt_path) as f:
        content = f.read()
    push_idx = content.find("(push 1)")
    if push_idx == -1:
        return evidence
    preamble = content[:push_idx]

    # Find axioms whose triggers involve the same operations
    op_smt_names = set()
    for op in smt_ops:
        smt_name = boogie_to_smt.get(op)
        if smt_name:
            op_smt_names.add(smt_name)

    relevant_axioms = _find_relevant_axioms(preamble, op_smt_names, gv)
    evidence["relevant_axioms"] = relevant_axioms

    # Analyze the trigger gap (heuristic — good for quick classification)
    evidence["trigger_gap"] = _analyze_trigger_gap(
        assert_text, smt_ops, relevant_axioms, gv
    )

    # Add axiom catalog info from the "with" annotation if available
    if with_annotation and "axiom_catalog" in with_annotation:
        relevant_funcs = _find_relevant_dafny_functions(
            assert_text, with_annotation["axiom_catalog"]
        )
        if relevant_funcs:
            evidence["relevant_dafny_functions"] = relevant_funcs

    return evidence


def extract_counterexample(
    without_artifacts: Path,
    name_map_path: Path,
    timeout: int = 30,
) -> dict | None:
    """Extract Z3 counterexample model from the failing VC.

    Finds the VC that returns unknown/sat, runs Z3 with (get-model),
    and maps the model values to Dafny-level names.
    """
    smt_path = without_artifacts / "output.smt2"
    if not smt_path.exists() or not name_map_path.exists():
        return None

    with open(name_map_path) as f:
        name_map = json.load(f)
    gv = name_map.get("variables", {})
    per_vc = name_map.get("perVc", [])

    with open(smt_path) as f:
        content = f.read()

    # Split into preamble + VCs
    push_idx = content.find("(push 1)")
    if push_idx == -1:
        return None
    preamble = content[:push_idx]

    # Parse VC blocks
    vc_blocks = []
    rest = content[push_idx:]
    depth = 0
    current_start = 0
    for m in re.finditer(r'\((push|pop) 1\)', rest):
        if m.group(1) == "push":
            if depth == 0:
                current_start = m.start()
            depth += 1
        else:
            depth -= 1
            if depth == 0:
                vc_blocks.append(rest[current_start:m.end()])

    if not vc_blocks:
        return None

    # Find the failing VC — run Z3 on each to find unknown/sat
    failing_vc_idx = None
    for i in range(len(vc_blocks) - 1, -1, -1):  # search from end (bigger VCs)
        import tempfile
        standalone = preamble + "\n" + vc_blocks[i]
        with tempfile.NamedTemporaryFile(mode="w", suffix=".smt2", delete=False) as f:
            f.write(standalone)
            tmp = f.name
        try:
            result = subprocess.run(
                ["z3", tmp, f"-T:{timeout}"],
                capture_output=True, text=True, timeout=timeout + 10,
            )
            first_line = result.stdout.strip().split("\n")[0] if result.stdout.strip() else ""
            if first_line in ("sat", "unknown", "timeout"):
                failing_vc_idx = i
                break
        except (subprocess.TimeoutExpired, Exception):
            failing_vc_idx = i
            break
        finally:
            Path(tmp).unlink(missing_ok=True)

    if failing_vc_idx is None:
        return None

    # Run Z3 with get-model on the failing VC
    vc_block = vc_blocks[failing_vc_idx]
    vc_with_model = vc_block.replace("(check-sat)", "(check-sat)\n(get-model)")
    standalone = preamble + "\n" + vc_with_model

    import tempfile
    with tempfile.NamedTemporaryFile(mode="w", suffix=".smt2", delete=False) as f:
        f.write(standalone)
        tmp = f.name

    try:
        result = subprocess.run(
            ["z3", tmp, f"-T:{timeout}"],
            capture_output=True, text=True, timeout=timeout + 10,
        )
    except (subprocess.TimeoutExpired, Exception):
        Path(tmp).unlink(missing_ok=True)
        return None
    finally:
        Path(tmp).unlink(missing_ok=True)

    model_text = result.stdout
    if not model_text.strip():
        return None

    # Build symbol table for this VC
    symbol_table = dict(gv)
    if failing_vc_idx < len(per_vc):
        symbol_table.update(per_vc[failing_vc_idx].get("variables", {}))

    # Parse and map the model
    return _parse_z3_model(model_text, symbol_table)


def _parse_z3_model(model_text: str, symbol_table: dict) -> dict:
    """Parse Z3 model text and map to Dafny names."""
    result = {
        "z3_result": "",
        "variables": {},
        "sequences": {},
        "functions": {},
    }

    lines = model_text.strip().split("\n")
    if not lines:
        return result
    result["z3_result"] = lines[0].strip()

    # Build reverse map for sequence operations
    seq_ops = {}
    for smt_name, boogie_name in symbol_table.items():
        if boogie_name.startswith("Seq#"):
            seq_ops[smt_name] = boogie_name

    # Parse simple assignments
    assignments = {}
    func_blocks = {}
    i = 0
    while i < len(lines):
        line = lines[i].strip()
        if " -> {" in line:
            # Function interpretation block
            name = line.split(" -> {")[0].strip()
            block_lines = [line]
            while i < len(lines) - 1:
                i += 1
                block_lines.append(lines[i].strip())
                if lines[i].strip().endswith("}"):
                    break
            func_blocks[name] = block_lines
        elif " -> " in line:
            parts = line.split(" -> ", 1)
            name = parts[0].strip()
            value = parts[1].strip()
            assignments[name] = value
        i += 1

    # Map variable assignments to Dafny names
    skip_types = {"T@TyTag!", "T@ClassName!", "T@TyTagFamily!", "T@Ty!val!",
                  "T@LayerType!", "T@DtCtorId!"}
    for smt_name, value in assignments.items():
        if any(value.startswith(t) for t in skip_types):
            continue
        # Skip Boogie assertion tracking flags (aux$$ names that are just true/false)
        if smt_name.startswith("aux$$"):
            continue

        dafny_name = symbol_table.get(smt_name, smt_name)
        if dafny_name == smt_name or dafny_name.startswith("$"):
            continue

        # Skip assertion/assume tracking — they're bookkeeping, not interesting
        if dafny_name.startswith("assert$$") or dafny_name.startswith("assume$$"):
            continue

        # Keep int values, Seq values, bool values
        if (value.isdigit() or value.startswith("(- ") or value.startswith("(-")
                or value.startswith("T@Seq!") or value in ("true", "false")):
            result["variables"][dafny_name] = value

    # Parse Seq#Length to map Seq!val!N → lengths
    seq_lengths = {}
    for smt_name, boogie_name in symbol_table.items():
        if boogie_name == "Seq#Length" and smt_name in func_blocks:
            for line in func_blocks[smt_name]:
                if " -> " in line and "else" not in line and "{" not in line:
                    parts = line.strip().split(" -> ")
                    if len(parts) == 2 and parts[0].strip().startswith("T@Seq!"):
                        seq_lengths[parts[0].strip()] = parts[1].strip()

    # Parse Seq#Take to understand slice relations
    seq_takes = {}
    for smt_name, boogie_name in symbol_table.items():
        if boogie_name == "Seq#Take" and smt_name in func_blocks:
            for line in func_blocks[smt_name]:
                if " -> " in line and "else" not in line and "{" not in line:
                    parts = line.strip().rsplit(" -> ", 1)
                    if len(parts) == 2:
                        args = parts[0].strip()
                        result_val = parts[1].strip()
                        seq_takes[args] = result_val

    # Build readable sequence info
    # Map Seq!val!N to variable names
    val_to_name = {}
    for dafny_name, value in result["variables"].items():
        if value.startswith("T@Seq!"):
            val_to_name[value] = dafny_name

    for seq_val, length in seq_lengths.items():
        name = val_to_name.get(seq_val, seq_val)
        result["sequences"][name] = {"value": seq_val, "length": length}

    # Helper to replace Seq!val!N with variable names using exact token matching
    def _map_seq_vals(text):
        """Replace T@Seq!val!N tokens with Dafny variable names (exact match only)."""
        # Sort by length descending to replace longer names first (T@Seq!val!15 before T@Seq!val!1)
        for val in sorted(val_to_name.keys(), key=len, reverse=True):
            # Use word boundary matching to avoid partial replacement
            text = re.sub(re.escape(val) + r'(?!\d)', val_to_name[val], text)
        return text

    # Add Seq#Take entries mapped to readable names
    take_entries = []
    for args, res in seq_takes.items():
        mapped = _map_seq_vals(f"Seq#Take({args}) = {res}")
        take_entries.append(mapped)
    if take_entries:
        result["functions"]["Seq#Take"] = take_entries

    # Parse user-defined functions (Sum, etc.)
    for smt_name, boogie_name in symbol_table.items():
        # Match exact function name — exclude #canCall, #requires variants
        if (boogie_name.startswith("_module.__default.")
                and "#" not in boogie_name
                and smt_name in func_blocks):
            sum_entries = []
            for line in func_blocks[smt_name]:
                if " -> " in line and "else" not in line and "{" not in line:
                    mapped = line.strip()
                    # Replace layer types
                    mapped = re.sub(r'T@LayerType!val!\d+\s*', '', mapped)
                    mapped = _map_seq_vals(mapped)
                    sum_entries.append(mapped.strip())
            if sum_entries:
                # Use just the function name (strip module prefix)
                short_name = boogie_name.replace("_module.__default.", "")
                result["functions"][short_name] = sum_entries

    return result


def _identify_smt_operations(assert_text: str) -> list[str]:
    """Identify which SMT operations a Dafny assertion involves."""
    ops = []

    # Sequence operations
    if "[.." in assert_text or "..]" in assert_text:
        ops.append("Seq#Take")
    if re.search(r'\[\d+\.\.\]', assert_text) or "[1..]" in assert_text:
        ops.append("Seq#Drop")
    if "+" in assert_text and "[" in assert_text:
        ops.append("Seq#Append")
    if re.search(r'\+ \[', assert_text) or re.search(r'\[.*\]$', assert_text):
        ops.append("Seq#Build")
    if re.search(r'\[\w+\]', assert_text) and "[.." not in assert_text:
        ops.append("Seq#Index")
    if "|" in assert_text:
        ops.append("Seq#Length")
    if "==" in assert_text:
        ops.append("Seq#Equal")

    return list(dict.fromkeys(ops))  # dedupe preserving order


def _dafny_assert_to_smt_terms(assert_text: str, global_vars: dict) -> dict:
    """Translate a Dafny assertion into the SMT terms that would appear."""
    terms = {}
    text = assert_text.replace("assert ", "").rstrip(";").strip()

    # Split on ==
    if "==" in text:
        parts = text.split("==", 1)
        lhs = parts[0].strip()
        rhs = parts[1].strip()
        terms["lhs_dafny"] = lhs
        terms["rhs_dafny"] = rhs
        terms["lhs_smt"] = _dafny_expr_to_smt(lhs)
        terms["rhs_smt"] = _dafny_expr_to_smt(rhs)

    return terms


def _dafny_expr_to_smt(expr: str) -> str:
    """Best-effort translation of a Dafny expression to SMT term notation.

    Handles nested expressions like:
      x[..i+1]              → Seq#Take(x, i+1)
      x[..i] + [x[i]]      → Seq#Append(Seq#Take(x, i), Seq#Build(Seq#Index(x, i)))
      (a + b[..|b|-1])      → Seq#Append(a, Seq#Take(b, Seq#Length(b)-1))
    """
    expr = expr.strip()

    # Strip outer parens if balanced
    if expr.startswith("(") and expr.endswith(")"):
        depth = 0
        balanced = True
        for i, c in enumerate(expr):
            if c == "(":
                depth += 1
            elif c == ")":
                depth -= 1
            if depth == 0 and i < len(expr) - 1:
                balanced = False
                break
        if balanced:
            expr = expr[1:-1].strip()

    # Check for top-level " + " FIRST (before slice patterns, since [..] regex is greedy)
    plus_idx = _find_toplevel_plus(expr)
    if plus_idx is not None:
        lhs = expr[:plus_idx].strip()
        rhs = expr[plus_idx + 3:].strip()
        return f"Seq#Append({_dafny_expr_to_smt(lhs)}, {_dafny_expr_to_smt(rhs)})"

    # Singleton literal: [x[i]] → Seq#Build(Seq#Index(x, i))
    m = re.match(r'^\[(.+)\[(.+)\]\]$', expr)
    if m:
        inner_base = m.group(1).strip()
        inner_idx = m.group(2).strip()
        if re.match(r'^\w+$', inner_base):
            return f"Seq#Build(Seq#Index({inner_base}, {inner_idx}))"

    # s[..expr] → Seq#Take(s, expr)
    m = re.match(r'^(\w+)\[\.\.(.+)\]$', expr)
    if m:
        base = m.group(1)
        slice_expr = m.group(2).strip()
        len_m = re.match(r'^\|(\w+)\|$', slice_expr)
        if len_m:
            return f"Seq#Take({base}, Seq#Length({len_m.group(1)}))"
        len_m2 = re.match(r'^\|(\w+)\|\s*-\s*(.+)$', slice_expr)
        if len_m2:
            return f"Seq#Take({base}, Seq#Length({len_m2.group(1)})-{len_m2.group(2)})"
        return f"Seq#Take({base}, {slice_expr})"

    # s[i..] → Seq#Drop(s, i)
    m = re.match(r'^(\w+)\[(\d+)\.\.\]$', expr)
    if m:
        return f"Seq#Drop({m.group(1)}, {m.group(2)})"

    return expr


def _find_toplevel_plus(expr: str) -> int | None:
    """Find the index of the first top-level ' + ' in an expression.

    Returns None if no top-level ' + ' exists.
    Respects parentheses () and brackets [].
    """
    depth = 0
    i = 0
    while i < len(expr) - 2:
        c = expr[i]
        if c in "([":
            depth += 1
        elif c in ")]":
            depth -= 1
        elif depth == 0 and expr[i:i+3] == " + ":
            return i
        i += 1
    return None


def _find_relevant_axioms(
    preamble: str,
    op_smt_names: set[str],
    global_vars: dict,
) -> list[dict]:
    """Find axioms in the SMT preamble whose triggers mention the given operations."""
    axioms = []

    # Find all forall axioms with :pattern clauses
    for m in re.finditer(
        r'\(assert\s+(?:\(=>\s+(\$generated@@\d+)\s+)?\(forall\s+\((.+?)\)\s+\(!',
        preamble,
    ):
        guard = m.group(1)
        bindings_raw = m.group(2)
        start = m.start()
        chunk = preamble[start:start + 5000]

        # Parse trigger patterns
        triggers_raw = re.findall(r':pattern\s+\(\s*\(([^)]+)\)', chunk)
        if not triggers_raw:
            continue

        # Check if the FIRST trigger (the primary pattern) mentions our operations
        # Only check the first trigger to avoid noise from secondary patterns
        relevant = False
        primary_trigger = triggers_raw[0] if triggers_raw else ""
        for op_name in op_smt_names:
            if op_name in primary_trigger:
                relevant = True
                break

        if not relevant:
            continue

        # Parse forall bindings for types
        bound_vars = {}
        type_map = {
            "T@Seq": "seq", "T@Set": "set", "Int": "int",
            "Bool": "bool", "T@Box": "box", "T@Ty": "type",
        }
        for bv in re.finditer(r'\((\$generated@@\d+)\s+(T@\w+|Int|Bool|Real)\)', bindings_raw):
            smt_type = bv.group(2)
            bound_vars[bv.group(1)] = type_map.get(smt_type, smt_type)

        # Resolve triggers
        resolved_triggers = []
        for t in triggers_raw:
            resolved = _resolve_smt_expr(t, global_vars, bound_vars)
            resolved_triggers.append(resolved)

        # Get qid
        qids = re.findall(r':qid\s+\|([^|]+)\|', chunk)
        qid = qids[-1] if qids else None

        # Get guard name
        guard_name = global_vars.get(guard, guard) if guard else "(ungated)"

        # Extract the body equality (what this axiom asserts)
        body_equalities = _extract_axiom_equalities(chunk, global_vars, bound_vars)

        axioms.append({
            "guard": guard_name,
            "qid": qid,
            "triggers": resolved_triggers[:5],
            "trigger_pattern": resolved_triggers[0] if resolved_triggers else "",
            "equalities": body_equalities[:3],
            "bound_var_types": list(bound_vars.values()),
        })

    return axioms


def _extract_axiom_equalities(chunk: str, global_vars: dict, bound_vars: dict) -> list[str]:
    """Extract equality assertions from an axiom body."""
    equalities = []

    # Find (= (Seq#Op ...) ...) patterns
    for m in re.finditer(r'\(=\s+\((\$generated@@\d+)\s+', chunk):
        func_smt = m.group(1)
        func_name = global_vars.get(func_smt, func_smt)
        if func_name.startswith("Seq#") or func_name.startswith("_module"):
            # Get some context
            eq_chunk = chunk[m.start():m.start() + 200]
            resolved = _resolve_smt_expr(eq_chunk[:150], global_vars, bound_vars)
            equalities.append(resolved)

    return equalities


def _resolve_smt_expr(expr: str, global_vars: dict, bound_vars: dict) -> str:
    """Resolve $generated@@N names in an SMT expression."""
    def _replace(m):
        name = m.group(0)
        if name in global_vars:
            resolved = global_vars[name]
            # Clean up common prefixes
            resolved = resolved.replace("_module.__default.", "")
            return resolved
        if name in bound_vars:
            return f"_{bound_vars[name]}_"
        return name

    resolved = re.sub(r'\$generated@@\d+', _replace, expr)
    # Clean up Boogie wrappers
    resolved = re.sub(r'\$LS\s*\(', '(', resolved)
    resolved = re.sub(r'\$LZ', '', resolved)
    resolved = re.sub(r'Lit_\d+\s+', '', resolved)
    resolved = re.sub(r'\$Box_\d+\s+', '', resolved)
    return resolved


def _analyze_trigger_gap(
    assert_text: str,
    smt_ops: list[str],
    relevant_axioms: list[dict],
    global_vars: dict,
) -> dict | None:
    """Analyze what trigger/axiom is missing that makes the assertion necessary."""
    gap = {
        "description": "",
        "needed_equality": "",
        "available_triggers": [],
        "missing_trigger": "",
    }

    text = assert_text.replace("assert ", "").rstrip(";").strip()

    # Classify the assertion pattern and determine the gap
    if "==" not in text:
        return None

    lhs, rhs = text.split("==", 1)
    lhs, rhs = lhs.strip(), rhs.strip()

    lhs_smt = _dafny_expr_to_smt(lhs)
    rhs_smt = _dafny_expr_to_smt(rhs)
    gap["needed_equality"] = f"{lhs_smt} == {rhs_smt}"

    # Collect all trigger patterns from relevant axioms
    all_triggers = []
    for ax in relevant_axioms:
        for t in ax.get("triggers", []):
            all_triggers.append(t)
    gap["available_triggers"] = list(set(all_triggers))[:10]

    # Pattern-specific gap analysis
    # s[..i+1] == s[..i] + [s[i]]  →  Seq#Take decomposition
    if re.search(r'\.\.\w\+1\]', text) and "+" in rhs:
        gap["pattern"] = "slice_extension"
        gap["description"] = (
            f"No axiom decomposes Seq#Take(s, n) into "
            f"Seq#Append(Seq#Take(s, n-1), Seq#Build(Seq#Index(s, n-1))). "
            f"Axioms exist for Seq#Take(Seq#Append(s,t), |s|) → s "
            f"(composition direction) but not the decomposition direction. "
            f"The trigger Seq#Take(s, n) only fires an axiom for the n==0 case."
        )
        gap["missing_trigger"] = (
            "Seq#Take(s, n) → Seq#Append(Seq#Take(s, n-1), Seq#Build(Seq#Index(s, n-1)))"
        )

    # s[..|s|] == s  →  full slice identity
    elif re.search(r'\.\.\|.*\|\]', lhs) and not re.search(r'[\+\[]', rhs):
        gap["pattern"] = "full_slice_identity"
        gap["description"] = (
            f"The axiom Seq#Take(s, Seq#Length(s)) == s exists but its trigger "
            f"requires both Seq#Take(s, n) and Seq#Length(s) to be in the e-graph "
            f"with n equal to Seq#Length(s). The solver does not automatically "
            f"simplify Seq#Take(s, Seq#Length(s)) to s without a matching trigger."
        )
        gap["missing_trigger"] = "Seq#Take(s, Seq#Length(s)) → s"

    # a + b == a  (empty concat identity)
    elif re.match(r'(\w+) \+ (\w+)$', lhs) and re.match(r'\w+$', rhs):
        gap["pattern"] = "empty_concat_identity"
        gap["description"] = (
            f"The solver knows |b|==0 from the branch condition but does not "
            f"conclude b==Seq#Empty(). The axiom Seq#Append(s, Seq#Empty())==s "
            f"requires the second argument to literally be Seq#Empty(), not just "
            f"a sequence with length 0. The solver cannot bridge the gap between "
            f"Seq#Length(b)==0 and b==Seq#Empty()."
        )
        gap["missing_trigger"] = (
            "Seq#Append(s, b) where Seq#Length(b)==0 → s"
        )

    # x == [x[0]] + x[1..]  →  cons decomposition
    elif re.match(r'\w+$', lhs) and ("[0]" in rhs or "[1..]" in rhs):
        gap["pattern"] = "cons_decomposition"
        gap["description"] = (
            f"No axiom decomposes a non-empty sequence into its head and tail: "
            f"s == Seq#Append(Seq#Build(Seq#Index(s, 0)), Seq#Drop(s, 1)). "
            f"The solver has both terms in the e-graph but no trigger connects them."
        )
        gap["missing_trigger"] = (
            "s → Seq#Append(Seq#Build(Seq#Index(s, 0)), Seq#Drop(s, 1))"
        )

    # a + b == (a + b[..|b|-1]) + [b[|b|-1]]  →  concat decomposition
    elif "+" in lhs and "[..|" in rhs:
        gap["pattern"] = "concat_last_element_decomposition"
        gap["description"] = (
            f"No axiom decomposes Seq#Append(a, b) by peeling the last element: "
            f"Seq#Append(a, b) == Seq#Append(Seq#Append(a, Seq#Take(b, |b|-1)), "
            f"Seq#Build(Seq#Index(b, |b|-1))). "
            f"This requires relating two different Seq#Append forms."
        )
        gap["missing_trigger"] = (
            "Seq#Append(a, b) → Seq#Append(Seq#Append(a, Seq#Take(b, |b|-1)), Seq#Build(Seq#Index(b, |b|-1)))"
        )

    # (s + [v])[..|s|] == s  →  prefix of append
    elif "[.." in lhs and "+" in lhs:
        gap["pattern"] = "prefix_of_append"
        gap["description"] = (
            f"The axiom Seq#Take(Seq#Append(s, t), |s|) == s exists with trigger "
            f"Seq#Take(Seq#Append(s, t), n). However, the term in the e-graph may "
            f"not match this pattern exactly because the append and take may be "
            f"constructed in a different order or the length condition is not "
            f"immediately visible."
        )
        gap["missing_trigger"] = (
            "Seq#Take(Seq#Append(s, t), Seq#Length(s)) → s"
        )

    else:
        # Generic gap
        gap["pattern"] = "unknown"
        gap["description"] = (
            f"The solver cannot derive the equality {lhs_smt} == {rhs_smt}. "
            f"The terms likely exist in the e-graph but no axiom trigger connects them."
        )

    return gap


def _find_relevant_dafny_functions(assert_text: str, axiom_catalog: dict) -> list[dict]:
    """Find Dafny functions mentioned in the assertion."""
    results = []
    text = assert_text.lower()
    for func_name, info in axiom_catalog.items():
        if func_name.lower() in text:
            results.append({
                "function": func_name,
                "axiom_count": info.get("axiom_count", 0),
                "triggers": info.get("all_triggers", [])[:5],
            })
    return results


# ═══════════════════════════════════════════════════════════════════════════
# Diagnosis — combine all evidence
# ═══════════════════════════════════════════════════════════════════════════


def diagnose_essential_assertion(
    assert_info: dict,
    problem_dir: Path,
    verified_path: Path,
    with_annotation: dict,
    ablation_result: dict,
) -> dict:
    """Full diagnosis for one essential assertion."""
    idx = assert_info["index"]
    evidence_dir = problem_dir / "evidence" / f"assert_{idx:02d}"
    evidence_dir.mkdir(parents=True, exist_ok=True)

    # 1. Save variants
    with_path = evidence_dir / "with_assertion.dfy"
    without_path = evidence_dir / "without_assertion.dfy"
    with_path.write_text(verified_path.read_text())
    create_variant(verified_path, assert_info, without_path)

    # 2. Run full logging on without variant
    without_artifacts = evidence_dir / "without_artifacts"
    print(f"    Running full logging on without variant...")
    run_full_logging(without_path, without_artifacts, timeout=60)

    # 3. Annotate the without variant
    without_ann_path = evidence_dir / "without_annotated.json"
    without_ann = run_annotate(without_artifacts, without_ann_path)

    # 4. Compare annotations
    annotation_diff = None
    if without_ann and with_annotation:
        annotation_diff = compare_annotations(with_annotation, without_ann)

    # 5. Extract SMT evidence from the "with" artifacts
    with_artifacts = problem_dir / "artifacts"
    smt_evidence = extract_smt_evidence(assert_info, with_artifacts, with_annotation)

    # 6. Extract counterexample model from failing VC
    print(f"    Extracting counterexample model...")
    counterexample = extract_counterexample(
        without_artifacts,
        without_artifacts / "name_map.json",
        timeout=30,
    )
    if counterexample:
        smt_evidence["counterexample"] = counterexample

    # 7. Build the diagnosis
    diagnosis = {
        "assert_index": idx,
        "line": assert_info["line"],
        "text": assert_info["text"],
    }

    # Error details
    if annotation_diff:
        errors = annotation_diff.get("new_errors", [])
        if errors:
            err = errors[0]
            diagnosis["failure"] = {
                "message": err.get("message", ""),
                "line": err.get("line"),
            }
            if err.get("related"):
                diagnosis["failure"]["related"] = err["related"].get("message", "")

        # Find the failing condition via AST mapping
        diagnosis["failing_condition"] = _find_failing_condition(annotation_diff)

    # SMT evidence
    diagnosis["smt_evidence"] = smt_evidence

    # Build human-readable evidence summary
    diagnosis["evidence_summary"] = _build_evidence_summary(
        assert_info, diagnosis, smt_evidence
    )

    # Write focused evidence bundle as markdown (for LLM consumption)
    evidence_md = _build_evidence_markdown(assert_info, diagnosis, smt_evidence)
    (evidence_dir / "evidence.md").write_text(evidence_md)

    # Save the full annotation diff for deep inspection
    diagnosis["files"] = {
        "with_assertion": str(with_path),
        "without_assertion": str(without_path),
        "without_artifacts": str(without_artifacts),
        "evidence_bundle": str(evidence_dir / "evidence.md"),
    }

    return diagnosis


def _build_evidence_markdown(assert_info: dict, diagnosis: dict, smt_evidence: dict) -> str:
    """Build a focused evidence bundle as markdown — designed for LLM analysis.

    This is the key deliverable: a self-contained document with everything
    an LLM (or human) needs to explain WHY the assertion is needed.
    """
    lines = []
    text = assert_info["text"]
    line_num = assert_info["line"]

    lines.append(f"# Evidence Bundle: {text}")
    lines.append(f"**Line {line_num}**")
    lines.append("")

    # 1. What the assertion says
    lines.append("## The Assertion")
    lines.append(f"```dafny")
    lines.append(f"{text}")
    lines.append(f"```")
    terms = smt_evidence.get("smt_encoding", {}).get("smt_terms", {})
    if terms:
        lines.append("")
        lines.append("**SMT encoding:**")
        if terms.get("lhs_dafny"):
            lines.append(f"- LHS: `{terms['lhs_dafny']}` → `{terms.get('lhs_smt', '?')}`")
        if terms.get("rhs_dafny"):
            lines.append(f"- RHS: `{terms['rhs_dafny']}` → `{terms.get('rhs_smt', '?')}`")
    lines.append("")

    # 2. What breaks without it
    lines.append("## What Breaks Without It")
    failure = diagnosis.get("failure", {})
    if failure:
        lines.append(f"**Dafny error:** {failure.get('message', '?')}")
        if failure.get("related"):
            lines.append(f"**Related:** {failure['related']}")
    fc = diagnosis.get("failing_condition")
    if fc:
        lines.append(f"**Failing condition:** `{fc['dafny']}` ({fc['type']})")
    lines.append("")

    # 3. Counterexample model
    cx = smt_evidence.get("counterexample")
    if cx:
        lines.append("## Counterexample Model (spurious)")
        lines.append(f"Z3 result: `{cx.get('z3_result', '?')}`")
        lines.append("")
        if cx.get("variables"):
            lines.append("**Variable assignments:**")
            lines.append("```")
            for name, value in sorted(cx["variables"].items()):
                lines.append(f"  {name} = {value}")
            lines.append("```")
            lines.append("")
        if cx.get("sequences"):
            lines.append("**Sequence lengths:**")
            lines.append("```")
            for name, info in sorted(cx["sequences"].items()):
                lines.append(f"  |{name}| = {info['length']}")
            lines.append("```")
            lines.append("")
        if cx.get("functions"):
            for func_name, entries in cx["functions"].items():
                lines.append(f"**{func_name} interpretation:**")
                lines.append("```")
                for entry in entries[:15]:
                    lines.append(f"  {entry}")
                lines.append("```")
                lines.append("")
    else:
        lines.append("## Counterexample Model")
        lines.append("No model available (timeout or solver returned unsat on isolated VC).")
        lines.append("")

    # 4. Relevant axioms
    axioms = smt_evidence.get("relevant_axioms", [])
    if axioms:
        lines.append(f"## Relevant Axioms ({len(axioms)} found)")
        lines.append("")
        lines.append("These are all axioms in the SMT preamble whose primary trigger")
        lines.append("pattern involves the same operations as the assertion:")
        lines.append("")
        for i, ax in enumerate(axioms):
            trigger = ax.get("trigger_pattern", "?")
            lines.append(f"### Axiom {i+1}")
            lines.append(f"- **Trigger:** `{trigger}`")
            if ax.get("equalities"):
                for eq in ax["equalities"][:2]:
                    lines.append(f"- **Body:** `{eq[:150]}`")
            if ax.get("qid"):
                lines.append(f"- **QID:** `{ax['qid']}`")
            lines.append("")

    # 5. Trigger gap analysis (heuristic)
    gap = smt_evidence.get("trigger_gap")
    if gap:
        lines.append("## Trigger Gap Analysis (heuristic)")
        lines.append(f"**Pattern:** `{gap.get('pattern', '?')}`")
        lines.append(f"**Description:** {gap.get('description', '')}")
        lines.append(f"**Needed:** `{gap.get('needed_equality', '')}`")
        lines.append(f"**Missing:** `{gap.get('missing_trigger', '')}`")
        lines.append("")

    # 6. Question for diagnosis
    lines.append("## Diagnosis Question")
    lines.append("")
    lines.append("Given the axioms above, explain precisely why the Z3 solver")
    lines.append(f"cannot derive `{text.replace('assert ', '').rstrip(';')}` on its own.")
    lines.append("What specific axiom or trigger pattern is missing from the")
    lines.append("SMT encoding that would allow the solver to derive this equality?")
    lines.append("Is this a fundamental limitation of the axiomatization, or a")
    lines.append("trigger/e-matching gap that could be fixed?")

    return "\n".join(lines)


def _find_failing_condition(annotation_diff: dict) -> dict | None:
    """Find the specific Dafny condition that fails from the annotation diff."""
    for vc_diff in annotation_diff.get("vc_diffs", []):
        vc_id = vc_diff.get("vc_id", "")
        if "Impl$$" not in vc_id:
            continue

        removed_details = vc_diff.get("removed_flag_details", {})

        # Look for invariant_maintained first (most precise)
        for fname, fdetail in removed_details.items():
            dafny = fdetail.get("dafny_meaning", "")
            if "$maintained" in fname and dafny:
                return {
                    "type": "invariant_maintained",
                    "dafny": dafny,
                    "vc_id": vc_id,
                    "flag": fname,
                    "bpl": fdetail.get("bpl_meaning", ""),
                }

        # Then postconditions
        for fname, fdetail in removed_details.items():
            dafny = fdetail.get("dafny_meaning", "")
            if fdetail.get("type") == "ensures" and dafny:
                return {
                    "type": "postcondition",
                    "dafny": dafny,
                    "vc_id": vc_id,
                    "flag": fname,
                    "bpl": fdetail.get("bpl_meaning", ""),
                }

    return None


def _build_evidence_summary(assert_info: dict, diagnosis: dict, smt_evidence: dict) -> str:
    """Build a human-readable evidence summary."""
    lines = []
    text = assert_info["text"]
    line = assert_info["line"]

    lines.append(f"ASSERTION: {text} (line {line})")
    lines.append("")

    # What fails
    failure = diagnosis.get("failure", {})
    if failure:
        lines.append(f"FAILURE: {failure.get('message', '?')}")
        if failure.get("related"):
            lines.append(f"  Related: {failure['related']}")

    fc = diagnosis.get("failing_condition")
    if fc:
        lines.append(f"FAILING CONDITION: {fc['dafny']} ({fc['type']})")
        lines.append(f"  VC: {fc['vc_id']}")
    lines.append("")

    # SMT encoding
    terms = smt_evidence.get("smt_encoding", {}).get("smt_terms", {})
    if terms:
        lines.append("SMT ENCODING:")
        if terms.get("lhs_dafny"):
            lines.append(f"  LHS: {terms['lhs_dafny']}")
            lines.append(f"     = {terms.get('lhs_smt', '?')}")
        if terms.get("rhs_dafny"):
            lines.append(f"  RHS: {terms['rhs_dafny']}")
            lines.append(f"     = {terms.get('rhs_smt', '?')}")
    lines.append("")

    # Trigger gap
    gap = smt_evidence.get("trigger_gap")
    if gap:
        lines.append(f"TRIGGER GAP ({gap.get('pattern', '?')}):")
        lines.append(f"  {gap.get('description', '')}")
        lines.append(f"  Needed: {gap.get('needed_equality', '')}")
        lines.append(f"  Missing: {gap.get('missing_trigger', '')}")
    lines.append("")

    # Relevant axioms
    axioms = smt_evidence.get("relevant_axioms", [])
    if axioms:
        lines.append(f"RELEVANT AXIOMS ({len(axioms)}):")
        for ax in axioms[:5]:
            trigger = ax.get("trigger_pattern", "?")
            lines.append(f"  trigger: {trigger[:100]}")
            for eq in ax.get("equalities", [])[:1]:
                lines.append(f"    body: {eq[:100]}")
    lines.append("")

    lines.append(f"SMT OPERATIONS: {smt_evidence.get('smt_encoding', {}).get('operations', [])}")

    # Counterexample summary
    cx = smt_evidence.get("counterexample")
    if cx:
        lines.append("")
        lines.append(f"COUNTEREXAMPLE ({cx.get('z3_result', '?')}):")
        for name, value in sorted(cx.get("variables", {}).items()):
            lines.append(f"  {name} = {value}")
        for name, info in sorted(cx.get("sequences", {}).items()):
            lines.append(f"  |{name}| = {info['length']}")

    return "\n".join(lines)


# ═══════════════════════════════════════════════════════════════════════════
# Main
# ═══════════════════════════════════════════════════════════════════════════


def main():
    parser = argparse.ArgumentParser(description="Ablation + Diagnosis pipeline")
    parser.add_argument("problem_dir", type=Path, help="Problem results directory")
    parser.add_argument("--timeout", type=int, default=30, help="Ablation timeout (seconds)")
    parser.add_argument("--ablation-only", action="store_true", help="Only run ablation, skip full diagnosis")
    args = parser.parse_args()

    problem_dir = args.problem_dir.resolve()
    verified_path = problem_dir / "artifacts" / "verified.dfy"
    with_ann_path = problem_dir / "artifacts" / "annotated_log.json"

    if not verified_path.exists():
        print(f"ERROR: {verified_path} not found")
        sys.exit(1)

    # Load the "with" annotation if available
    with_annotation = None
    if with_ann_path.exists():
        with_annotation = json.loads(with_ann_path.read_text())

    # Phase 1: Extract all assert statements
    asserts = extract_asserts(verified_path)
    print(f"Found {len(asserts)} assert statements in {verified_path.name}")

    # Phase 2: Ablation
    ablation_dir = problem_dir / "ablation"
    ablation_dir.mkdir(parents=True, exist_ok=True)

    essential = []
    non_essential = []

    for a in asserts:
        variant_path = ablation_dir / f"without_{a['index']:02d}.dfy"
        create_variant(verified_path, a, variant_path)

        t0 = time.time()
        result = run_ablation(variant_path, timeout=args.timeout)
        elapsed = time.time() - t0

        status = result.get("result", "unknown")
        is_essential = status != "pass"

        a["essential"] = is_essential
        a["ablation_status"] = status
        a["ablation_time"] = round(elapsed, 1)
        a["ablation_errors"] = result.get("errors", [])

        marker = "ESSENTIAL" if is_essential else "ok"
        print(f"  [{a['index']:2d}] L{a['line']:3d} {marker:9s} ({elapsed:.1f}s): {a['text'][:70]}")

        if is_essential:
            essential.append(a)
        else:
            non_essential.append(a)

    print(f"\n{'='*60}")
    print(f"Essential: {len(essential)}/{len(asserts)}")
    for a in essential:
        print(f"  L{a['line']:3d}: {a['text']}")
    print(f"{'='*60}\n")

    # Save ablation results
    ablation_results = {
        "total_asserts": len(asserts),
        "essential_count": len(essential),
        "non_essential_count": len(non_essential),
        "essential": [
            {"index": a["index"], "line": a["line"], "text": a["text"],
             "status": a["ablation_status"], "errors": a["ablation_errors"]}
            for a in essential
        ],
        "non_essential": [
            {"index": a["index"], "line": a["line"], "text": a["text"]}
            for a in non_essential
        ],
    }
    (problem_dir / "ablation_results.json").write_text(json.dumps(ablation_results, indent=2))

    if args.ablation_only:
        print("Ablation-only mode — skipping full diagnosis.")
        return

    # Phase 3: Full diagnosis
    print(f"Running full diagnosis on {len(essential)} essential assertions...\n")

    diagnoses = []
    for a in essential:
        print(f"  Diagnosing [{a['index']:2d}] L{a['line']}: {a['text'][:60]}...")
        diagnosis = diagnose_essential_assertion(
            a, problem_dir, verified_path, with_annotation,
            {"result": a["ablation_status"], "errors": a["ablation_errors"]},
        )
        diagnoses.append(diagnosis)

        # Print the evidence summary
        summary = diagnosis.get("evidence_summary", "")
        for line in summary.split("\n"):
            if line.strip():
                print(f"    {line}")
        print()

    # Save full diagnosis
    full_report = {
        "problem_dir": str(problem_dir),
        "verified_file": str(verified_path),
        "total_asserts": len(asserts),
        "essential_count": len(essential),
        "diagnoses": diagnoses,
    }
    report_path = problem_dir / "diagnosis.json"
    report_path.write_text(json.dumps(full_report, indent=2))
    print(f"\nDiagnosis written to {report_path}")


if __name__ == "__main__":
    main()

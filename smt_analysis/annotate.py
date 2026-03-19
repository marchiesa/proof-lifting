#!/usr/bin/env python3
"""
Annotate verification artifacts with Dafny-level names.

Combines information from THREE sources:
  1. output.bpl    — Human-readable Boogie IL with {:id} annotations, loop structure,
                     trigger patterns { ... }, and source location comments
  2. name_map.json — Per-VC mapping of $generated@@N → Boogie names
  3. ast_mapping.json — Boogie assertion IDs → Dafny source text + expression ASTs

The key insight: the BPL file is the Rosetta Stone. The SMT file is the BPL compiled
down to $generated@@N names. Named assertions in SMT are just boolean flags — their
content is in guarded axioms (for assumptions) or inline in the VC body (for assertions).

Usage:
    python3 smt_analysis/annotate.py \
        --bpl artifacts/output.bpl \
        --name-map artifacts/name_map.json \
        --ast-mapping artifacts/ast_mapping.json \
        --smt artifacts/output.smt2 \
        --dafny-output artifacts/dafny_output.txt \
        -o annotated_log.json
"""

import argparse
import json
import re
import sys
from collections import defaultdict
from pathlib import Path


# ── Boogie→Dafny known function translations ──────────────────────────────

BOOGIE_TO_DAFNY_EXPR = {
    "Seq#Length": "|{0}|",
    "Seq#Take": "{0}[..{1}]",
    "Seq#Drop": "{0}[{1}..]",
    "Seq#Index": "{0}[{1}]",
    "Seq#Build": "{0} + [{1}]",
    "Seq#Append": "{0} + {1}",
    "Seq#Equal": "{0} == {1}",
    "Seq#Empty": "[]",
    "Seq#Singleton": "[{0}]",
    "Seq#Contains": "{1} in {0}",
    "Seq#Update": "{0}[{1} := {2}]",
}


# ═══════════════════════════════════════════════════════════════════════════
# BPL Parsing — extract structured information from Boogie IL
# ═══════════════════════════════════════════════════════════════════════════


def parse_bpl(bpl_path: str) -> dict:
    """Parse BPL file to extract procedures, assertions, loops, triggers."""
    with open(bpl_path) as f:
        bpl = f.read()
    lines = bpl.split("\n")

    result = {
        "procedures": [],
        "axiom_ids": {},     # id → axiom text from {:id "idN"} on axioms
        "assertion_ids": {}, # id → {text, type, source_line} from {:id "idN"} on assert/assume/ensures/requires
        "functions": [],     # ghost function declarations
    }

    # ── Extract ALL {:id "..."} annotations ──
    for i, line in enumerate(lines):
        m = re.search(r'\{:id\s+"(id\d+)"\}', line)
        if not m:
            continue
        id_val = m.group(1)
        stripped = line.strip()

        # Determine type and extract text
        if stripped.startswith("axiom"):
            # Axiom — extract the quantified body
            result["axiom_ids"][id_val] = {
                "type": "axiom",
                "line": i + 1,
                "text": _extract_axiom_summary(stripped),
            }
        elif stripped.startswith("assert"):
            result["assertion_ids"][id_val] = {
                "type": "assert",
                "line": i + 1,
                "text": _extract_assertion_text(stripped, id_val),
                "boogie_text": stripped,
            }
        elif stripped.startswith("assume"):
            result["assertion_ids"][id_val] = {
                "type": "assume",
                "line": i + 1,
                "text": _extract_assertion_text(stripped, id_val),
                "boogie_text": stripped,
            }
        elif "requires" in stripped:
            result["assertion_ids"][id_val] = {
                "type": "requires",
                "line": i + 1,
                "text": _extract_pre_post_text(stripped, "requires"),
                "boogie_text": stripped,
            }
        elif "ensures" in stripped:
            result["assertion_ids"][id_val] = {
                "type": "ensures",
                "line": i + 1,
                "text": _extract_pre_post_text(stripped, "ensures"),
                "boogie_text": stripped,
            }
        else:
            result["assertion_ids"][id_val] = {
                "type": "other",
                "line": i + 1,
                "text": stripped[:200],
            }

    # ── Extract procedures ──
    proc_pattern = re.compile(
        r'procedure\s+(?:\{[^}]*\}\s+)*(\S+)\s*\(', re.MULTILINE
    )
    for m in proc_pattern.finditer(bpl):
        proc_name = m.group(1)
        # Find verboseName if present
        verbose = ""
        vm = re.search(r'\{:verboseName\s+"([^"]+)"\}', bpl[max(0, m.start()-200):m.end()])
        if vm:
            verbose = vm.group(1)
        result["procedures"].append({
            "name": proc_name,
            "verbose_name": verbose,
            "line": bpl[:m.start()].count("\n") + 1,
        })

    # ── Extract loops with structure ──
    # Look for "while (true)" blocks and their context
    loops = []
    for i, line in enumerate(lines):
        if "while statement" in line and line.strip().startswith("//"):
            # Extract source location
            loc_m = re.search(r'(\S+\.dfy)\((\d+),(\d+)\)', line)
            source = ""
            if loc_m:
                source = f"{loc_m.group(1)}:{loc_m.group(2)}"

            # Look for invariants in the next ~30 lines
            invs = []
            for j in range(i + 1, min(i + 40, len(lines))):
                if "invariant" in lines[j] and not lines[j].strip().startswith("//"):
                    inv_text = lines[j].strip()
                    if "free invariant" in inv_text:
                        continue  # Skip frame conditions
                    invs.append(inv_text)
                if lines[j].strip() == "{":
                    break

            loops.append({
                "bpl_line": i + 1,
                "source": source,
                "invariants": invs,
            })
    result["loops"] = loops

    return result


def _extract_assertion_text(line: str, id_val: str) -> str:
    """Extract the condition text from an assert/assume {:id} line."""
    # Remove the {:id "..."} and leading keyword
    text = re.sub(r'\{:id\s+"[^"]+"\}\s*', '', line)
    text = re.sub(r'^(assert|assume)\s+', '', text).strip()
    text = text.rstrip(";").strip()
    return _clean_boogie_expr(text)


def _extract_pre_post_text(line: str, keyword: str) -> str:
    """Extract text from requires/ensures line."""
    text = re.sub(r'\{[^}]*\}\s*', '', line)  # Remove all attributes
    text = re.sub(rf'^(free\s+)?{keyword}\s+', '', text.strip()).strip()
    text = text.rstrip(";").strip()
    return _clean_boogie_expr(text)


def _extract_axiom_summary(line: str) -> str:
    """Extract a summary of an axiom."""
    # Just return first 200 chars, cleaned
    text = re.sub(r'\{[^}]*\}\s*', '', line)
    text = re.sub(r'^axiom\s+', '', text.strip())
    return text[:200]


def _clean_boogie_expr(expr: str) -> str:
    """Clean up a Boogie expression for human readability."""
    # Remove module prefix
    expr = expr.replace("_module.__default.", "")
    # Remove Lit wrappers
    expr = re.sub(r'LitInt\((\d+)\)', r'\1', expr)
    expr = re.sub(r'Lit\(([^)]+)\)', r'\1', expr)
    # Remove $Unbox wrappers
    expr = re.sub(r'\$Unbox\(([^)]+)\):\s*int', r'\1', expr)
    # Clean SSA suffixes for readability (but keep them distinguishable)
    expr = re.sub(r'#(\d+)', r'_v\1', expr)
    return expr


# ═══════════════════════════════════════════════════════════════════════════
# SMT Preamble Parsing — extract guarded axioms and trigger patterns
# ═══════════════════════════════════════════════════════════════════════════


def parse_smt_preamble(smt_path: str, name_map: dict) -> dict:
    """Parse the SMT preamble (before first reset/push) for axiom/trigger info."""
    with open(smt_path) as f:
        content = f.read()

    # Find the global preamble (before first (push 1))
    push_idx = content.find("(push 1)")
    if push_idx == -1:
        push_idx = content.find("(set-info :boogie-vc-id")
    if push_idx == -1:
        push_idx = len(content)
    preamble = content[:push_idx]

    # Build global symbol table
    symbol_table = _build_symbol_table(name_map, vc_number=None)

    # Extract guarded axioms: (assert (=> FLAG (forall ... :pattern ... :qid ...)))
    axioms = []
    for m in re.finditer(
        r'\(assert\s+\(=>\s+(\$generated@@\d+)\s+\(forall', preamble
    ):
        guard = m.group(1)
        guard_name = symbol_table.get(guard, guard)

        # Extract chunk around this axiom for trigger/qid parsing
        start = m.start()
        chunk = preamble[start:start + 5000]

        # Parse forall-bound variables: (($generated@@81 T@Seq) ($generated@@82 T@Seq) ...)
        bound_vars = {}
        forall_bindings = re.search(r'\(forall\s+\((.+?)\)\s+\(!', chunk)
        if forall_bindings:
            for bv in re.finditer(r'\((\$generated@@\d+)\s+(T@\w+|Int|Bool|Real)\)', forall_bindings.group(1)):
                smt_type = bv.group(2)
                # Simplify type names
                type_map = {"T@Seq": "seq", "T@Set": "set", "T@Map": "map",
                            "T@Ty": "type", "T@Ref": "ref", "T@Box": "box",
                            "T@Heap": "heap", "T@Field": "field",
                            "Int": "int", "Bool": "bool", "Real": "real"}
                bound_vars[bv.group(1)] = type_map.get(smt_type, smt_type)
        # Also parse nested forall bindings (inner quantifiers)
        for inner in re.finditer(r'\(forall\s+\((\(\$generated@@\d+\s+\S+\)\s*)+\)', chunk):
            for bv in re.finditer(r'\((\$generated@@\d+)\s+(T@\w+|Int|Bool|Real)\)', inner.group(0)):
                if bv.group(1) not in bound_vars:
                    smt_type = bv.group(2)
                    type_map = {"T@Seq": "seq", "T@Set": "set", "T@Map": "map",
                                "T@Ty": "type", "T@Ref": "ref", "T@Box": "box",
                                "T@Heap": "heap", "T@Field": "field",
                                "Int": "int", "Bool": "bool", "Real": "real"}
                    bound_vars[bv.group(1)] = type_map.get(smt_type, smt_type)

        # Get outermost :qid (the axiom-level one, usually last)
        qids = re.findall(r':qid\s+\|([^|]+)\|', chunk)
        outermost_qid = qids[-1] if qids else None

        # Get ALL :pattern values
        triggers_raw = re.findall(r':pattern\s+\(\s*\(([^)]+)\)', chunk)
        triggers_resolved = []  # with _module.__default. still present (for function ID)
        triggers = []           # cleaned for display
        for t in triggers_raw:
            def _resolve_smt_name(x):
                name = x.group(0)
                # First try global symbol table (functions, constants)
                if name in symbol_table:
                    return symbol_table[name]
                # Then try bound variable types
                if name in bound_vars:
                    return f"_{bound_vars[name]}_"
                return name
            resolved = re.sub(r'\$generated@@\d+', _resolve_smt_name, t)
            triggers_resolved.append(resolved)
            # Clean up for display
            cleaned = resolved.replace("_module.__default.", "")
            cleaned = re.sub(r'\$LS\s+', '', cleaned)
            cleaned = re.sub(r'Lit_\d+\s+', '', cleaned)
            cleaned = re.sub(r'\$Box_\d+\s+', '$Box ', cleaned)
            triggers.append(cleaned)

        # Determine which Dafny function this axiom defines (use unclean triggers)
        dafny_func = _identify_axiom_function(guard_name, triggers_resolved, symbol_table)

        axioms.append({
            "guard_smt": guard,
            "guard_name": guard_name,
            "dafny_function": dafny_func,
            "triggers": triggers,
            "qid": outermost_qid,
        })

    # Extract VC IDs from the full file (they appear in each VC section)
    vc_ids_raw = re.findall(r':boogie-vc-id\s+(\S+)', content)
    # Clean trailing parens that might get captured
    vc_ids = [v.rstrip(")") for v in vc_ids_raw]

    return {
        "axioms": axioms,
        "vc_ids": vc_ids,
        "symbol_table_size": len(symbol_table),
    }


def _identify_axiom_function(guard_name: str, triggers: list[str], symbol_table: dict) -> str:
    """Identify which Dafny function a guarded axiom defines."""
    # The guard is assume$$idN — look for _module.__default.FuncName in triggers
    # Priority: explicit module-qualified function names over anything else
    for t in triggers:
        m = re.search(r'_module\.__default\.(\w+)', t)
        if m:
            name = m.group(1)
            # Remove #canCall, #requires suffixes
            name = re.sub(r'#(canCall|requires)$', '', name)
            return name

    # Fallback: look for non-Boogie-internal function names
    skip = {"Seq", "Set", "Map", "Reads", "LitInt", "Lit", "select", "MultiSet",
            "ISet", "IMap", "Box", "Unbox", "Int", "Bool", "Real", "Char"}
    for t in triggers:
        for word in re.findall(r'\b([A-Z]\w+)\b', t):
            if word not in skip and not word.startswith("T@") and "#" not in word:
                return word

    return guard_name


def _build_symbol_table(name_map: dict, vc_number: int | None) -> dict:
    """Build $generated@@N → Boogie name symbol table."""
    merged = dict(name_map.get("variables", {}))
    if vc_number is not None:
        for vc in name_map.get("perVc", []):
            if vc.get("vc") == vc_number:
                merged.update(vc.get("variables", {}))
                break
    return merged


# ═══════════════════════════════════════════════════════════════════════════
# AST Mapping — link Boogie IDs to Dafny source
# ═══════════════════════════════════════════════════════════════════════════


def parse_ast_mapping(ast_mapping: dict) -> dict:
    """Extract structured info from AST mapping."""
    result = {
        "id_to_dafny": {},      # boogieId → Dafny text
        "id_to_location": {},   # boogieId → {line, col, file}
        "variables": {},        # Dafny name → {type, boogieName}
        "functions": {},        # Dafny name → boogieName
    }

    for method in ast_mapping.get("methods", []):
        # Variables
        for var_name, var_info in method.get("variables", {}).items():
            result["variables"][var_info.get("dafnyName", var_name)] = {
                "type": var_info.get("type", "?"),
                "boogieName": var_info.get("boogieName", ""),
            }

        # Invariants
        for inv in method.get("invariants", []):
            bid = inv.get("boogieId", "")
            if bid:
                result["id_to_dafny"][bid] = inv.get("text", "")
                result["id_to_dafny"][bid + "$maintained"] = f"invariant maintained: {inv.get('text', '')}"
                result["id_to_dafny"][bid + "$established"] = f"invariant established: {inv.get('text', '')}"
                if inv.get("location"):
                    result["id_to_location"][bid] = inv["location"]

        # Assertions
        for asrt in method.get("assertions", []):
            bid = asrt.get("boogieId", "")
            if bid:
                result["id_to_dafny"][bid] = f"assert {asrt.get('text', '')}"
                if asrt.get("location"):
                    result["id_to_location"][bid] = asrt["location"]

        # Requires
        for req in method.get("requires", []):
            bid = req.get("boogieId", "")
            if bid:
                result["id_to_dafny"][bid] = f"requires {req.get('text', '')}"
                if req.get("location"):
                    result["id_to_location"][bid] = req["location"]

        # Ensures
        for ens in method.get("ensures", []):
            bid = ens.get("boogieId", "")
            if bid:
                result["id_to_dafny"][bid] = f"ensures {ens.get('text', '')}"
                if ens.get("location"):
                    result["id_to_location"][bid] = ens["location"]

    # Top-level functions
    for func in ast_mapping.get("functions", []):
        result["functions"][func.get("dafnyName", "")] = func.get("boogieName", "")

    return result


# ═══════════════════════════════════════════════════════════════════════════
# Per-VC Analysis — combine all sources for each verification condition
# ═══════════════════════════════════════════════════════════════════════════


def build_vc_annotations(
    name_map: dict,
    ast_info: dict,
    bpl_info: dict,
    smt_info: dict,
) -> list[dict]:
    """Build per-VC annotations combining all sources."""
    vc_ids = smt_info.get("vc_ids", [])
    per_vc = name_map.get("perVc", [])

    # Build mapping from perVc index to VC ID
    # perVc entries are ordered and correspond 1:1 to vc_ids from the SMT file
    # (perVc numbers may start at 2+ due to Boogie's internal numbering,
    #  but their order matches the SMT vc_ids order)
    annotated_vcs = []
    for i, vc_entry in enumerate(per_vc):
        vc_num = vc_entry["vc"]
        vc_id = vc_ids[i] if i < len(vc_ids) else f"vc_{vc_num}"

        # Build per-VC symbol table
        sym = _build_symbol_table(name_map, vc_num)

        # Classify variables into categories
        program_vars = {}   # Dafny program variables
        assertion_flags = {} # assert$$idN / assume$$idN flags
        control_flow = {}    # anon*_correct blocks
        boogie_internals = {} # $Heap, $ModifiesFrame, etc.

        for smt_name, boogie_name in vc_entry.get("variables", {}).items():
            if "@@" not in smt_name:
                continue
            n = int(smt_name.split("@@")[1])
            # Only look at VC-local variables (high-numbered ones)
            # Global variables are shared and not VC-specific
            if n < 2234:
                continue

            if boogie_name.startswith("assert$$") or boogie_name.startswith("assume$$"):
                # Extract the ID: assert$$id62 → id62
                id_val = boogie_name.split("$$")[1]
                # Look up in BPL and AST mapping
                bpl_text = bpl_info["assertion_ids"].get(id_val, {}).get("text", "")
                dafny_text = ast_info["id_to_dafny"].get(id_val, "")
                assertion_flags[boogie_name] = {
                    "smt_name": smt_name,
                    "boogie_id": id_val,
                    "bpl_meaning": bpl_text[:300] if bpl_text else "",
                    "dafny_meaning": dafny_text[:300] if dafny_text else "",
                    "type": bpl_info["assertion_ids"].get(id_val, {}).get("type", "?"),
                }
            elif boogie_name.endswith("_correct"):
                control_flow[boogie_name] = smt_name
            elif boogie_name.startswith("$") or boogie_name.startswith("_"):
                boogie_internals[boogie_name] = smt_name
            else:
                # Program variable — strip SSA suffix for display
                clean = re.sub(r'#\d+(@\d+)?$', '', boogie_name)
                program_vars[boogie_name] = {
                    "smt_name": smt_name,
                    "dafny_name": _boogie_var_to_dafny(boogie_name, ast_info),
                    "ssa_version": boogie_name,
                }

        # Determine VC purpose from assertion flags
        purpose = _determine_vc_purpose(vc_id, assertion_flags, ast_info)

        # Count assertion types
        assertion_types = defaultdict(int)
        for flag_info in assertion_flags.values():
            assertion_types[flag_info["type"]] += 1

        annotated_vcs.append({
            "vc_index": vc_num,
            "vc_id": vc_id,
            "purpose": purpose,
            "program_variables": program_vars,
            "assertion_flags": assertion_flags,
            "control_flow_blocks": list(control_flow.keys()),
            "assertion_type_counts": dict(assertion_types),
        })

    return annotated_vcs


def _boogie_var_to_dafny(boogie_name: str, ast_info: dict) -> str:
    """Map Boogie variable name to Dafny name."""
    # Strip SSA: "xSum#0@2" → "xSum"
    base = re.sub(r'#\d+(@\d+)?$', '', boogie_name)
    # Check AST mapping
    if base in ast_info["variables"]:
        return ast_info["variables"][base].get("type", base)
    return base


def _determine_vc_purpose(vc_id: str, assertion_flags: dict, ast_info: dict) -> str:
    """Determine what a VC is trying to prove."""
    # First: use the VC ID directly
    if "Impl$$" in vc_id:
        method = vc_id.replace("Impl$$_module.__default.", "")
        # Find postcondition
        for flag_name, flag_info in assertion_flags.items():
            if flag_info["type"] == "ensures" and flag_info["dafny_meaning"]:
                return f"Method {method}: {flag_info['dafny_meaning']}"
        return f"Method {method} implementation correctness"

    if "CheckWellformed$$" in vc_id:
        func = vc_id.replace("CheckWellformed$$_module.__default.", "")
        return f"Well-formedness of {func}"

    # Look for invariant maintenance/establishment
    for flag_name, flag_info in assertion_flags.items():
        dm = flag_info.get("dafny_meaning", "")
        if "maintained" in dm:
            return dm
        if "established" in dm:
            return dm

    return vc_id


# ═══════════════════════════════════════════════════════════════════════════
# Function-level axiom catalog
# ═══════════════════════════════════════════════════════════════════════════


def build_axiom_catalog(smt_info: dict, ast_info: dict) -> dict:
    """Build a catalog of axioms per Dafny function with trigger patterns."""
    catalog = defaultdict(list)
    for axiom in smt_info.get("axioms", []):
        func = axiom["dafny_function"]
        catalog[func].append({
            "guard": axiom["guard_name"],
            "triggers": axiom["triggers"],
            "qid": axiom["qid"],
        })

    # Add Dafny function names from AST mapping
    enriched = {}
    for func_name, axiom_list in catalog.items():
        # Check if this matches a known Dafny function
        dafny_name = func_name
        for dname, bname in ast_info["functions"].items():
            if func_name in bname or func_name == dname:
                dafny_name = dname
                break

        enriched[dafny_name] = {
            "axioms": axiom_list,
            "axiom_count": len(axiom_list),
            "all_triggers": [t for a in axiom_list for t in a["triggers"]],
        }

    return enriched


# ═══════════════════════════════════════════════════════════════════════════
# Dafny output parsing
# ═══════════════════════════════════════════════════════════════════════════


def parse_dafny_output(dafny_output_path: str) -> dict:
    """Parse Dafny verify output for errors and verification results."""
    try:
        with open(dafny_output_path) as f:
            text = f.read()
    except FileNotFoundError:
        return {"errors": [], "summary": "file not found"}

    errors = []
    for line in text.split("\n"):
        line = line.strip()
        if not line:
            continue
        # Match error lines: file(line,col): Error: message
        m = re.match(r'(\S+\.dfy)\((\d+),(\d+)\):\s*(Error|Warning):\s*(.*)', line)
        if m:
            errors.append({
                "file": m.group(1),
                "line": int(m.group(2)),
                "col": int(m.group(3)),
                "severity": m.group(4),
                "message": m.group(5),
            })
        # Related location
        m = re.match(r'(\S+\.dfy)\((\d+),(\d+)\):\s*Related location:\s*(.*)', line)
        if m and errors:
            errors[-1]["related"] = {
                "file": m.group(1),
                "line": int(m.group(2)),
                "message": m.group(4),
            }

    # Summary line
    summary = ""
    m = re.search(r'Dafny program verifier finished with (\d+) verified, (\d+) error', text)
    if m:
        summary = f"{m.group(1)} verified, {m.group(2)} errors"
    elif "timed out" in text.lower():
        summary = "timeout"

    return {"errors": errors, "summary": summary, "raw": text}


# ═══════════════════════════════════════════════════════════════════════════
# Main pipeline
# ═══════════════════════════════════════════════════════════════════════════


def annotate_full(
    bpl_path: str | None,
    name_map_path: str,
    ast_mapping_path: str,
    smt_path: str | None = None,
    dafny_output_path: str | None = None,
) -> dict:
    """Full annotation pipeline combining all sources."""
    # Load name map and AST mapping (always required)
    with open(name_map_path) as f:
        name_map = json.load(f)
    with open(ast_mapping_path) as f:
        ast_mapping_raw = json.load(f)

    # Parse AST mapping
    ast_info = parse_ast_mapping(ast_mapping_raw)

    # Parse BPL if available
    bpl_info = {"procedures": [], "axiom_ids": {}, "assertion_ids": {}, "loops": []}
    if bpl_path and Path(bpl_path).exists():
        bpl_info = parse_bpl(bpl_path)

    # Parse SMT preamble if available
    smt_info = {"axioms": [], "vc_ids": []}
    if smt_path and Path(smt_path).exists():
        smt_info = parse_smt_preamble(smt_path, name_map)

    # Build per-VC annotations
    vc_annotations = build_vc_annotations(name_map, ast_info, bpl_info, smt_info)

    # Build axiom catalog
    axiom_catalog = build_axiom_catalog(smt_info, ast_info)

    # Build symbol table summary (most useful entries)
    symbol_summary = _build_symbol_summary(name_map)

    # Parse Dafny output
    dafny_info = {}
    if dafny_output_path:
        dafny_info = parse_dafny_output(dafny_output_path)

    # Combine everything
    return {
        "summary": {
            "total_vcs": len(vc_annotations),
            "procedures": [p["name"] for p in bpl_info["procedures"]],
            "loops_found": len(bpl_info["loops"]),
            "axioms_found": len(smt_info["axioms"]),
            "dafny_functions": list(ast_info["functions"].keys()),
            "dafny_variables": {
                k: v["type"] for k, v in ast_info["variables"].items()
                if not k.startswith("##")
            },
            "verification_result": dafny_info.get("summary", ""),
        },
        "dafny_errors": dafny_info.get("errors", []),
        "axiom_catalog": axiom_catalog,
        "vcs": vc_annotations,
        "loops": bpl_info["loops"],
        "assertion_id_table": {
            id_val: {
                "bpl": info.get("text", ""),
                "dafny": ast_info["id_to_dafny"].get(id_val, ""),
                "type": info.get("type", ""),
            }
            for id_val, info in bpl_info["assertion_ids"].items()
        },
        "symbol_table": symbol_summary,
    }


def _build_symbol_summary(name_map: dict) -> dict:
    """Build a summary of the most useful symbol table entries."""
    global_vars = name_map.get("variables", {})

    categories = {
        "dafny_functions": {},    # Module functions
        "seq_operations": {},     # Seq#Length, Seq#Take, etc.
        "set_operations": {},     # Set#Card, etc.
        "type_info": {},          # TBool, TInt, etc.
    }

    for smt_name, boogie_name in global_vars.items():
        if "_module.__default." in boogie_name:
            clean = boogie_name.replace("_module.__default.", "")
            categories["dafny_functions"][clean] = smt_name
        elif boogie_name.startswith("Seq#"):
            categories["seq_operations"][boogie_name] = smt_name
        elif boogie_name.startswith("Set#") or boogie_name.startswith("Map#"):
            categories["set_operations"][boogie_name] = smt_name
        elif boogie_name.startswith("T") and len(boogie_name) <= 10:
            categories["type_info"][boogie_name] = smt_name

    return categories


def main():
    parser = argparse.ArgumentParser(
        description="Annotate verification artifacts with Dafny-level names"
    )
    parser.add_argument("--bpl", help="Boogie IL file (.bpl)")
    parser.add_argument("--name-map", required=True, help="Name map JSON")
    parser.add_argument("--ast-mapping", required=True, help="AST mapping JSON")
    parser.add_argument("--smt", help="SMT-LIB file (.smt2)")
    parser.add_argument("--dafny-output", help="Dafny verify output")
    parser.add_argument("-o", "--output", help="Output JSON file")
    args = parser.parse_args()

    result = annotate_full(
        bpl_path=args.bpl,
        name_map_path=args.name_map,
        ast_mapping_path=args.ast_mapping,
        smt_path=args.smt,
        dafny_output_path=args.dafny_output,
    )

    output_json = json.dumps(result, indent=2)

    if args.output:
        with open(args.output, "w") as f:
            f.write(output_json)
        s = result["summary"]
        print(
            f"Annotated {s['total_vcs']} VCs, "
            f"{s['axioms_found']} axioms, "
            f"{s['loops_found']} loops "
            f"-> {args.output}",
            file=sys.stderr,
        )
    else:
        print(output_json)


if __name__ == "__main__":
    main()

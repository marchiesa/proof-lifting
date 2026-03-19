#!/usr/bin/env python3
"""
Inline non-recursive lemmas in verified Dafny files.

Non-recursive lemmas are essentially packaged assertions. Inlining them
makes ablation more granular — we can test individual assertions instead
of opaque lemma calls.

Usage:
    # Inline lemmas for specific problems
    python3 smt_analysis/inline_lemmas.py --names 0006_1017_A 0009_1041_A

    # Inline lemmas for all verified problems
    python3 smt_analysis/inline_lemmas.py --all --workers 5

    # Dry run (show what would be inlined, don't modify files)
    python3 smt_analysis/inline_lemmas.py --all --dry-run
"""

import argparse
import json
import re
import subprocess
import sys
import time
from concurrent.futures import ProcessPoolExecutor, as_completed
from pathlib import Path

PROJ_ROOT = Path(__file__).parent.parent.resolve()
DATASET_DIR = PROJ_ROOT / "dataset"
RESULTS_DIR = PROJ_ROOT / "smt_analysis" / "results"
DOTNET = os.environ.get("DOTNET8", os.environ.get("DOTNET", "dotnet"))
DAFNY_DLL = PROJ_ROOT / "dafny-source" / "Binaries" / "Dafny.dll"


def parse_lemmas(code: str) -> list[dict]:
    """Parse lemma definitions from Dafny code.

    Returns list of {name, params, requires, ensures, body, start_line, end_line, is_recursive}.
    """
    lemmas = []
    lines = code.split("\n")
    i = 0
    while i < len(lines):
        # Match lemma definition
        m = re.match(r'\s*lemma\s+(\w+)\s*(\(.*)', lines[i])
        if not m:
            # Also match multi-line: lemma Name\n  (params)
            m = re.match(r'\s*lemma\s+(\w+)\s*$', lines[i])
            if m and i + 1 < len(lines) and lines[i + 1].strip().startswith("("):
                pass  # will be handled below
            else:
                i += 1
                continue

        name = m.group(1)
        start_line = i

        # Collect the full lemma text until we find the matching closing brace
        # or a bare ensures/requires followed by { ... }
        brace_depth = 0
        lemma_lines = []
        found_body_start = False
        body_start_line = None
        j = i
        while j < len(lines):
            line = lines[j]
            lemma_lines.append(line)

            for ch in line:
                if ch == '{':
                    if not found_body_start:
                        found_body_start = True
                        body_start_line = j
                    brace_depth += 1
                elif ch == '}':
                    brace_depth -= 1

            if found_body_start and brace_depth == 0:
                break
            j += 1

        end_line = j
        lemma_text = "\n".join(lemma_lines)

        # Check if body is empty (just { })
        if body_start_line is not None:
            body_lines = lines[body_start_line:end_line + 1]
            body_text = "\n".join(body_lines)
            # Strip the outer braces
            body_inner = re.sub(r'^\s*\{', '', body_text, count=1)
            body_inner = re.sub(r'\}\s*$', '', body_inner)
        else:
            body_inner = ""

        # Parse requires and ensures
        requires = []
        ensures = []
        for line in lemma_lines:
            stripped = line.strip()
            if stripped.startswith("requires "):
                requires.append(stripped[len("requires "):])
            elif stripped.startswith("ensures "):
                ensures.append(stripped[len("ensures "):])

        # Parse parameters
        # Collect everything between the first ( and matching )
        param_text = ""
        paren_depth = 0
        collecting = False
        for line in lemma_lines:
            for ch in line:
                if ch == '(' and not collecting:
                    collecting = True
                    paren_depth = 1
                elif ch == '(' and collecting:
                    paren_depth += 1
                    param_text += ch
                elif ch == ')' and collecting:
                    paren_depth -= 1
                    if paren_depth == 0:
                        collecting = False
                        break
                    param_text += ch
                elif collecting:
                    param_text += ch
            if not collecting and param_text:
                break

        # Parse individual parameters: name: type
        params = []
        for p in param_text.split(","):
            p = p.strip()
            if not p:
                continue
            pm = re.match(r'(\w+)\s*:\s*(.+)', p)
            if pm:
                params.append({"name": pm.group(1), "type": pm.group(2).strip()})

        # Check if recursive (lemma name appears in body)
        is_recursive = bool(re.search(rf'\b{name}\s*\(', body_inner))

        lemmas.append({
            "name": name,
            "params": params,
            "requires": requires,
            "ensures": ensures,
            "body": body_inner.strip(),
            "start_line": start_line,
            "end_line": end_line,
            "is_recursive": is_recursive,
            "full_text": lemma_text,
        })

        i = end_line + 1
        continue

    return lemmas


def find_lemma_calls(code: str, lemma_name: str) -> list[dict]:
    """Find all calls to a lemma in the code.

    Returns list of {line, args_text, full_match}.
    """
    calls = []
    lines = code.split("\n")
    for i, line in enumerate(lines):
        # Match: LemmaName(arg1, arg2, ...);
        # Need to handle multi-line calls and nested parens
        m = re.search(rf'\b{lemma_name}\s*\(', line)
        if not m:
            continue

        # Check this isn't the lemma definition itself
        if re.match(r'\s*lemma\s+' + lemma_name, line):
            continue

        # Extract arguments — handle nested parens
        start = m.end() - 1  # position of opening (
        text = "\n".join(lines[i:min(i + 10, len(lines))])
        paren_depth = 0
        args_start = m.end()
        args_end = None
        for pos, ch in enumerate(text[m.start():], m.start()):
            if ch == '(':
                paren_depth += 1
            elif ch == ')':
                paren_depth -= 1
                if paren_depth == 0:
                    args_end = pos
                    break

        if args_end is not None:
            args_text = text[args_start:args_end]
            calls.append({
                "line": i,
                "args_text": args_text,
                "full_match": text[m.start():args_end + 1],
            })

    return calls


def parse_call_args(args_text: str) -> list[str]:
    """Parse comma-separated arguments, respecting nested parens/brackets."""
    args = []
    depth = 0
    current = ""
    for ch in args_text:
        if ch in "([{":
            depth += 1
            current += ch
        elif ch in ")]}":
            depth -= 1
            current += ch
        elif ch == "," and depth == 0:
            args.append(current.strip())
            current = ""
        else:
            current += ch
    if current.strip():
        args.append(current.strip())
    return args


def substitute_params(text: str, params: list[dict], args: list[str]) -> str:
    """Substitute formal parameters with actual arguments in text.

    Avoids variable capture by first renaming bound variables (in forall/exists)
    that clash with parameter names.
    """
    result = text

    # Collect all actual argument variable names to detect clashes
    arg_vars = set()
    for arg in args:
        arg_vars.update(re.findall(r'\b([a-zA-Z_]\w*)\b', arg))

    # Rename bound variables in forall/exists that clash with args
    # Pattern: forall VAR | ... or forall VAR :: ...
    for bound_m in re.finditer(r'\b(forall|exists)\s+(\w+)\s*([|:])', result):
        bound_var = bound_m.group(2)
        if bound_var in arg_vars or any(bound_var == p["name"] for p in params):
            # Rename to avoid capture
            fresh = f"__{bound_var}__"
            # Only rename within this quantifier's scope (approximate: rest of expression)
            # This is a best-effort approach
            before = result[:bound_m.start()]
            after = result[bound_m.start():]
            after = re.sub(rf'\b{bound_var}\b', fresh, after)
            result = before + after

    for param, arg in zip(params, args):
        # Word-boundary replacement to avoid partial matches
        result = re.sub(rf'\b{param["name"]}\b', f'({arg})', result)

    return result


def inline_lemma(code: str, lemma: dict, dry_run: bool = False) -> tuple[str, list[str]]:
    """Inline a non-recursive lemma.

    Returns (modified_code, list_of_changes).
    """
    if lemma["is_recursive"]:
        return code, [f"SKIP {lemma['name']}: recursive"]

    calls = find_lemma_calls(code, lemma["name"])
    if not calls:
        return code, [f"SKIP {lemma['name']}: no calls found"]

    changes = []
    lines = code.split("\n")

    # Process calls in reverse order (so line numbers stay valid)
    for call in reversed(calls):
        args = parse_call_args(call["args_text"])
        if len(args) != len(lemma["params"]):
            changes.append(f"SKIP call at line {call['line'] + 1}: arg count mismatch "
                          f"({len(args)} vs {len(lemma['params'])})")
            continue

        # Build inlined code: only inline ensures as assertions.
        # Body is needed to help the solver prove the ensures, so include it too.
        # But requires are preconditions — skip them (they should already hold).
        inlined_lines = []

        # Add body statements (substituted) — these help the solver
        if lemma["body"]:
            body_sub = substitute_params(lemma["body"], lemma["params"], args)
            for bline in body_sub.split("\n"):
                bline = bline.strip()
                if bline:
                    inlined_lines.append(bline)

        # Add ensures as assertions (the actual facts we want)
        for ens in lemma["ensures"]:
            # Skip requires-like ensures (forall preconditions)
            if ens.strip().startswith("forall") and "|" in ens and "::" in ens:
                # Check if it's a simple well-formedness condition (e.g., forall i | ... :: |x[i]| >= 4)
                # These are precondition-like — skip them
                if "requires" not in ens and (">=" in ens or "<=" in ens or ">" in ens or "<" in ens):
                    # Heuristic: if the ensures is a simple bound/size check, skip it
                    pass
                else:
                    ens_sub = substitute_params(ens, lemma["params"], args)
                    ens_sub = _clean_parens(ens_sub)
                    inlined_lines.append(f"assert {ens_sub};")
            else:
                ens_sub = substitute_params(ens, lemma["params"], args)
                ens_sub = _clean_parens(ens_sub)
                inlined_lines.append(f"assert {ens_sub};")

        # Build the replacement text with proper indentation
        call_line = lines[call["line"]]
        indent = len(call_line) - len(call_line.lstrip())
        indent_str = " " * indent

        replacement = []
        replacement.append(f"{indent_str}// Inlined from {lemma['name']}({call['args_text'].strip()})")
        for il in inlined_lines:
            replacement.append(f"{indent_str}{il}")

        # Replace the call line
        lines[call["line"]] = "\n".join(replacement)
        changes.append(f"INLINE call at line {call['line'] + 1}: "
                      f"{lemma['name']}({call['args_text'].strip()[:60]})")

    # Remove the lemma definition
    # Replace with empty lines to preserve line numbers for other edits
    for j in range(lemma["start_line"], lemma["end_line"] + 1):
        lines[j] = ""
    changes.append(f"REMOVE lemma definition {lemma['name']} "
                  f"(lines {lemma['start_line'] + 1}-{lemma['end_line'] + 1})")

    # Clean up multiple blank lines
    result = "\n".join(lines)
    result = re.sub(r'\n{4,}', '\n\n\n', result)

    return result, changes


def _clean_parens(expr: str) -> str:
    """Remove unnecessary outer parens from substituted expressions."""
    # Remove parens around simple variable names: (x) -> x
    expr = re.sub(r'\((\w+)\)', r'\1', expr)
    # Remove parens around simple indexed: (x[i]) -> x[i]
    expr = re.sub(r'\((\w+\[[^\]]+\])\)', r'\1', expr)
    return expr


def verify_file(dfy_file: Path, timeout: int = 60) -> tuple[bool, str]:
    """Run dafny verify and return (success, output)."""
    try:
        result = subprocess.run(
            [DOTNET, str(DAFNY_DLL), "verify", str(dfy_file),
             "--verification-time-limit", str(timeout)],
            capture_output=True, text=True, timeout=timeout + 30,
        )
        output = result.stdout + result.stderr
        success = "0 errors" in output
        return success, output
    except subprocess.TimeoutExpired:
        return False, "TIMEOUT"
    except Exception as e:
        return False, f"EXCEPTION: {e}"


def process_problem(problem_name: str, dry_run: bool = False) -> dict:
    """Inline lemmas for a single problem."""
    result_dir = RESULTS_DIR / problem_name
    verified_file = result_dir / "verified.dfy"

    if not verified_file.exists():
        return {"problem": problem_name, "status": "skip", "reason": "no verified.dfy"}

    code = verified_file.read_text()
    lemmas = parse_lemmas(code)

    if not lemmas:
        return {"problem": problem_name, "status": "skip", "reason": "no lemmas found"}

    non_recursive = [l for l in lemmas if not l["is_recursive"]]
    if not non_recursive:
        return {
            "problem": problem_name,
            "status": "skip",
            "reason": f"all {len(lemmas)} lemmas are recursive",
        }

    all_changes = []
    modified_code = code

    for lemma in non_recursive:
        modified_code, changes = inline_lemma(modified_code, lemma, dry_run)
        all_changes.extend(changes)

    if dry_run:
        return {
            "problem": problem_name,
            "status": "dry_run",
            "lemmas_total": len(lemmas),
            "lemmas_inlinable": len(non_recursive),
            "changes": all_changes,
        }

    # Save backup
    backup = result_dir / "verified_before_inline.dfy"
    backup.write_text(code)

    # Write inlined version
    inlined_file = result_dir / "verified_inlined.dfy"
    inlined_file.write_text(modified_code)

    # Verify the inlined version
    ok, output = verify_file(inlined_file)

    if ok:
        # Replace verified.dfy with inlined version
        verified_file.write_text(modified_code)
        status = "inlined"
    else:
        # Keep original, save error
        (result_dir / "inline_error.txt").write_text(output)
        status = "inline_failed"

    return {
        "problem": problem_name,
        "status": status,
        "lemmas_total": len(lemmas),
        "lemmas_inlined": len(non_recursive),
        "changes": all_changes,
        "verified_after_inline": ok,
    }


def main():
    parser = argparse.ArgumentParser(description="Inline non-recursive lemmas in verified Dafny files")
    group = parser.add_mutually_exclusive_group(required=True)
    group.add_argument("--names", type=str, nargs="+", help="Problem names to process")
    group.add_argument("--all", action="store_true", help="Process all verified problems")
    parser.add_argument("--workers", type=int, default=5, help="Parallel workers (default: 5)")
    parser.add_argument("--dry-run", action="store_true", help="Show what would be inlined without modifying files")
    args = parser.parse_args()

    # Find problems to process
    if args.names:
        names = args.names
    else:
        names = []
        for rd in sorted(RESULTS_DIR.iterdir()):
            if not rd.is_dir():
                continue
            vr = rd / "verify_result.json"
            if vr.exists():
                try:
                    r = json.loads(vr.read_text())
                    if r.get("verified"):
                        names.append(rd.name)
                except json.JSONDecodeError:
                    pass

    print(f"Processing {len(names)} problems {'(dry run)' if args.dry_run else ''}")

    results = []
    if args.workers == 1 or args.dry_run:
        for name in names:
            r = process_problem(name, dry_run=args.dry_run)
            results.append(r)
            print(f"  [{name}] {r['status']}: {r.get('changes', [r.get('reason', '')])[0] if r.get('changes') or r.get('reason') else ''}")
    else:
        with ProcessPoolExecutor(max_workers=args.workers) as executor:
            futures = {executor.submit(process_problem, name, args.dry_run): name for name in names}
            for future in as_completed(futures):
                r = future.result()
                results.append(r)
                print(f"  [{r['problem']}] {r['status']}")

    # Summary
    inlined = sum(1 for r in results if r["status"] == "inlined")
    failed = sum(1 for r in results if r["status"] == "inline_failed")
    skipped = sum(1 for r in results if r["status"] == "skip")
    dry = sum(1 for r in results if r["status"] == "dry_run")

    print()
    if args.dry_run:
        inlinable = sum(1 for r in results if r.get("lemmas_inlinable", 0) > 0)
        print(f"Dry run: {inlinable} problems have inlinable lemmas, {skipped} skipped")
        for r in results:
            if r.get("changes"):
                print(f"\n  {r['problem']}:")
                for c in r["changes"]:
                    print(f"    {c}")
    else:
        print(f"Inlined: {inlined}, Failed: {failed}, Skipped: {skipped}")


if __name__ == "__main__":
    main()

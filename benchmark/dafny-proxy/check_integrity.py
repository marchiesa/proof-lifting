#!/usr/bin/env python3
"""
Integrity checker for the Dafny benchmark proxy.

Compares a submitted file against the original task file to ensure the LLM
has not modified the code logic, method signatures, or formal specification.

Allowed additions:
  - invariant clauses (including multi-line)
  - assert statements (including assert ... by { ... } blocks)
  - assume statements
  - ghost var declarations and assignments
  - lemma blocks (top-level)
  - ghost function/method/predicate blocks
  - helper function/method blocks not in the original
  - decreases clauses inside while loops
  - forall proof statements (forall x | P(x) ensures Q(x) { ... })
  - calc blocks
  - bare lemma/function calls (not assignments, not control flow)

Everything else must remain identical.
"""

import re
import sys
import json
import difflib
from typing import List, Tuple, Optional


def read_file(path: str) -> str:
    with open(path, "r") as f:
        return f.read()


def strip_comments(text: str) -> str:
    """Remove single-line and multi-line comments."""
    # Remove multi-line comments
    text = re.sub(r'/\*.*?\*/', '', text, flags=re.DOTALL)
    # Remove single-line comments
    text = re.sub(r'//[^\n]*', '', text)
    return text


def normalize_whitespace(text: str) -> str:
    """Collapse all whitespace to single spaces and strip."""
    return re.sub(r'\s+', ' ', text).strip()


class DafnyParser:
    """
    A lightweight parser for Dafny files that extracts top-level blocks
    and provides stripping of proof-only constructs.
    """

    def __init__(self, source: str):
        self.source = source
        self.lines = source.splitlines()

    def find_brace_block(self, start_line: int) -> Tuple[int, int]:
        """
        Given a starting line, find the matching closing brace.
        Returns (start_line, end_line) inclusive.
        """
        depth = 0
        found_open = False
        for i in range(start_line, len(self.lines)):
            line = self.lines[i]
            # Count braces outside of strings (simplified)
            in_string = False
            in_char = False
            j = 0
            while j < len(line):
                c = line[j]
                if c == '"' and not in_char:
                    in_string = not in_string
                elif c == '\'' and not in_string:
                    in_char = not in_char
                elif not in_string and not in_char:
                    if c == '{':
                        depth += 1
                        found_open = True
                    elif c == '}':
                        depth -= 1
                        if depth == 0 and found_open:
                            return (start_line, i)
                j += 1
        return (start_line, len(self.lines) - 1)

    def extract_top_level_blocks(self) -> List[dict]:
        """
        Extract top-level blocks: methods, functions, predicates, lemmas,
        classes, modules, etc.
        Returns list of {type, name, start, end, content}.
        """
        blocks = []
        i = 0
        while i < len(self.lines):
            line = self.lines[i].strip()
            # Skip blank lines and comments
            if not line or line.startswith('//') or line.startswith('/*'):
                i += 1
                continue

            # Match top-level declarations
            m = re.match(
                r'^(ghost\s+)?(method|function|predicate|lemma|class|module|datatype|type|trait|iterator|codatatype|newtype|const|import|include)\b',
                line
            )
            if m:
                ghost_prefix = m.group(1) or ''
                block_type = (ghost_prefix + m.group(2)).strip()

                # Extract name
                name_match = re.search(
                    r'(?:method|function|predicate|lemma|class|module|datatype|type|trait|iterator|codatatype|newtype|const)\s+(?:{{:.*?}}\s*)?(\w+)',
                    line
                )
                name = name_match.group(1) if name_match else f"_anon_{i}"

                # For blocks that have braces, find the full extent
                if any(kw in block_type for kw in
                       ['method', 'function', 'predicate', 'lemma', 'class',
                        'module', 'trait', 'iterator']):
                    start, end = self.find_brace_block(i)
                    blocks.append({
                        'type': block_type,
                        'name': name,
                        'start': start,
                        'end': end,
                        'content': '\n'.join(self.lines[start:end + 1])
                    })
                    i = end + 1
                else:
                    # Single-line or until next top-level
                    blocks.append({
                        'type': block_type,
                        'name': name,
                        'start': i,
                        'end': i,
                        'content': self.lines[i]
                    })
                    i += 1
            else:
                i += 1

        return blocks


def strip_proof_constructs(text: str) -> str:
    """
    Remove all proof constructs from Dafny source, leaving only
    the code logic and specification.

    This is the core of the integrity checker. It strips:
    - invariant lines (including multi-line continuations)
    - decreases clauses inside loop context
    - assert statements (including assert ... by { ... })
    - assume statements
    - ghost var declarations
    - calc blocks
    - forall proof statements
    - bare lemma/function calls
    """
    lines = text.splitlines()
    result = []
    i = 0

    while i < len(lines):
        line = lines[i]
        stripped = line.strip()

        # Skip empty lines — preserve them
        if not stripped:
            result.append(line)
            i += 1
            continue

        # Skip single-line comments
        if stripped.startswith('//'):
            i += 1
            continue

        # Skip ghost var declarations (including multi-line)
        if re.match(r'^ghost\s+var\b', stripped):
            # May span multiple lines until semicolon
            while i < len(lines) and ';' not in lines[i]:
                i += 1
            i += 1  # skip the line with semicolon
            continue

        # Skip invariant lines (including multi-line)
        if re.match(r'^invariant\b', stripped):
            i = _skip_clause(lines, i)
            continue

        # Skip decreases clauses (inside loops)
        if re.match(r'^decreases\b', stripped):
            i = _skip_clause(lines, i)
            continue

        # Skip assert statements (including assert ... by { ... })
        if re.match(r'^assert\b', stripped):
            i = _skip_assert_or_assume(lines, i)
            continue

        # Skip assume statements
        if re.match(r'^assume\b', stripped):
            i = _skip_assert_or_assume(lines, i)
            continue

        # Skip calc blocks: calc { ... }
        if re.match(r'^calc\b', stripped):
            i = _skip_brace_block(lines, i)
            continue

        # Skip forall proof statements: forall ... ensures ... { ... }
        if re.match(r'^forall\b', stripped):
            i = _skip_brace_block(lines, i)
            continue

        result.append(line)
        i += 1

    return '\n'.join(result)


def _skip_clause(lines: List[str], start: int) -> int:
    """
    Skip a clause like `invariant expr` or `decreases expr`.
    These may span multiple lines. The clause ends when we hit:
    - another invariant/decreases/modifies/reads/ensures/requires
    - an opening brace {
    - a code statement (var, if, while, return, etc.)
    - a blank line followed by non-continuation
    """
    i = start + 1
    while i < len(lines):
        stripped = lines[i].strip()
        if not stripped:
            i += 1
            continue
        # If this looks like a new clause, statement, or block, stop
        if re.match(
            r'^(invariant|decreases|modifies|reads|ensures|requires|var|ghost|if|else|while|for|return|assert|assume|match|print|expect|calc|forall|{|})',
            stripped
        ):
            return i
        # If the line looks like a continuation of the expression, skip it
        i += 1
    return i


def _skip_assert_or_assume(lines: List[str], start: int) -> int:
    """
    Skip assert/assume statements, including:
    - `assert expr;`
    - `assert expr by { ... }`
    - multi-line variants
    """
    line = lines[start].strip()

    # Check if this has a `by {` block
    # First, find the semicolon or `by` keyword
    i = start
    accumulated = ''
    while i < len(lines):
        accumulated += ' ' + lines[i].strip()

        # If we find `by` followed by `{`, skip the brace block
        if re.search(r'\bby\s*\{', accumulated):
            # Find where `by {` starts and skip the full brace block
            return _skip_brace_block_from_open(lines, i, accumulated)

        # If we find a semicolon, done
        if ';' in lines[i]:
            return i + 1

        i += 1

    return i


def _skip_brace_block(lines: List[str], start: int) -> int:
    """Skip a block that contains { ... }, finding balanced braces."""
    depth = 0
    found_open = False
    i = start
    while i < len(lines):
        for c in lines[i]:
            if c == '{':
                depth += 1
                found_open = True
            elif c == '}':
                depth -= 1
                if depth == 0 and found_open:
                    return i + 1
        i += 1
    return i


def _skip_brace_block_from_open(lines: List[str], current_line: int, accumulated: str) -> int:
    """Skip from the current position when we know there's an opening brace in accumulated."""
    depth = 0
    found_open = False

    # Count braces in the accumulated text up to current_line
    for c in accumulated:
        if c == '{':
            depth += 1
            found_open = True
        elif c == '}':
            depth -= 1
            if depth == 0 and found_open:
                return current_line + 1

    # Continue scanning from next line
    i = current_line + 1
    while i < len(lines):
        for c in lines[i]:
            if c == '{':
                depth += 1
                found_open = True
            elif c == '}':
                depth -= 1
                if depth == 0 and found_open:
                    return i + 1
        i += 1
    return i


def extract_spec_blocks(parser: DafnyParser) -> List[dict]:
    """Extract specification blocks: predicates, functions (non-ghost), datatypes."""
    blocks = parser.extract_top_level_blocks()
    spec_blocks = []
    for b in blocks:
        if b['type'] in ('predicate', 'function', 'datatype', 'type',
                         'newtype', 'codatatype', 'const', 'import', 'include'):
            spec_blocks.append(b)
    return spec_blocks


def extract_methods(parser: DafnyParser) -> List[dict]:
    """Extract method blocks."""
    blocks = parser.extract_top_level_blocks()
    return [b for b in blocks if b['type'] == 'method']


def check_integrity(original_path: str, submitted_path: str) -> Tuple[bool, str]:
    """
    Check that the submitted file has not modified the code logic or specification.

    Returns (ok, message).
    - ok=True means the file is acceptable.
    - ok=False means the file was modified, and message explains what changed.
    """
    try:
        original_src = read_file(original_path)
        submitted_src = read_file(submitted_path)
    except FileNotFoundError as e:
        return False, f"File not found: {e}"

    # Parse both files
    orig_parser = DafnyParser(strip_comments(original_src))
    sub_parser = DafnyParser(strip_comments(submitted_src))

    errors = []

    # 1. Check that all original spec blocks are present and unchanged
    orig_specs = extract_spec_blocks(orig_parser)
    sub_specs = extract_spec_blocks(sub_parser)

    orig_spec_map = {b['name']: b for b in orig_specs}
    sub_spec_map = {b['name']: b for b in sub_specs}

    for name, orig_block in orig_spec_map.items():
        if name not in sub_spec_map:
            errors.append(f"Specification block '{name}' was removed")
            continue
        orig_norm = normalize_whitespace(orig_block['content'])
        sub_norm = normalize_whitespace(sub_spec_map[name]['content'])
        if orig_norm != sub_norm:
            errors.append(f"Specification block '{name}' was modified")

    # 2. Check that method signatures match
    orig_methods = extract_methods(orig_parser)
    sub_methods = extract_methods(sub_parser)

    orig_method_map = {b['name']: b for b in orig_methods}
    sub_method_map = {b['name']: b for b in sub_methods}

    for name, orig_method in orig_method_map.items():
        if name not in sub_method_map:
            errors.append(f"Method '{name}' was removed")
            continue

        # Extract the signature (everything before the first '{')
        orig_sig = orig_method['content'].split('{')[0] if '{' in orig_method['content'] else orig_method['content']
        sub_sig = sub_method_map[name]['content'].split('{')[0] if '{' in sub_method_map[name]['content'] else sub_method_map[name]['content']

        orig_sig_norm = normalize_whitespace(orig_sig)
        sub_sig_norm = normalize_whitespace(sub_sig)

        if orig_sig_norm != sub_sig_norm:
            errors.append(f"Method '{name}' signature was modified")

    # 3. Check that the code logic is identical after stripping proof constructs
    orig_stripped = strip_proof_constructs(strip_comments(original_src))
    sub_stripped = strip_proof_constructs(strip_comments(submitted_src))

    orig_code_norm = normalize_whitespace(orig_stripped)
    sub_code_norm = normalize_whitespace(sub_stripped)

    if orig_code_norm != sub_code_norm:
        # Generate a diff to show what changed
        diff = difflib.unified_diff(
            orig_stripped.splitlines(),
            sub_stripped.splitlines(),
            fromfile='original (stripped)',
            tofile='submitted (stripped)',
            lineterm=''
        )
        diff_text = '\n'.join(list(diff)[:50])  # Limit diff output
        errors.append(f"Code logic was modified after stripping proof constructs:\n{diff_text}")

    if errors:
        return False, '\n'.join(errors)

    return True, "Integrity check passed"


def strip_new_top_level_blocks(original_src: str, submitted_src: str) -> str:
    """
    From the submitted source, remove any top-level blocks (lemmas, ghost functions,
    ghost methods, ghost predicates, helper functions/methods) that don't exist
    in the original source.

    Returns the submitted source with new blocks removed.
    """
    orig_parser = DafnyParser(strip_comments(original_src))
    sub_parser = DafnyParser(strip_comments(submitted_src))

    orig_blocks = orig_parser.extract_top_level_blocks()
    sub_blocks = sub_parser.extract_top_level_blocks()

    orig_names = {b['name'] for b in orig_blocks}

    # Lines to remove (ranges)
    remove_ranges = []
    for b in sub_blocks:
        if b['name'] not in orig_names:
            # This is a new block added by the LLM
            if any(kw in b['type'] for kw in
                   ['lemma', 'ghost', 'function', 'method', 'predicate']):
                remove_ranges.append((b['start'], b['end']))

    if not remove_ranges:
        return submitted_src

    # Remove the lines
    lines = strip_comments(submitted_src).splitlines()
    result = []
    for i, line in enumerate(lines):
        skip = False
        for start, end in remove_ranges:
            if start <= i <= end:
                skip = True
                break
        if not skip:
            result.append(line)

    return '\n'.join(result)


def check_integrity_detailed(original_path: str, submitted_path: str) -> dict:
    """
    Detailed integrity check returning structured results.
    """
    ok, message = check_integrity(original_path, submitted_path)
    return {
        'passed': ok,
        'message': message,
        'original_path': original_path,
        'submitted_path': submitted_path
    }


if __name__ == '__main__':
    if len(sys.argv) != 3:
        print(f"Usage: {sys.argv[0]} <original.dfy> <submitted.dfy>", file=sys.stderr)
        sys.exit(2)

    ok, message = check_integrity(sys.argv[1], sys.argv[2])
    if ok:
        print("PASS:", message)
        sys.exit(0)
    else:
        print("FAIL:", message)
        sys.exit(1)

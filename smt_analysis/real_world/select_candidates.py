#!/usr/bin/env python3
"""Select 100 candidate functions from CodeSearchNet Python dataset.

Criteria:
- 5-25 lines of code (excluding docstrings/comments)
- Contains a loop (for/while)
- Works with basic data types (lists, ints, strings)
- Minimal external dependencies (no imports, minimal self usage)
- Clear algorithmic pattern mappable to a quirk type

Saves selected candidates to candidates.json with metadata.
"""

import json
import re
from collections import Counter, defaultdict
from datasets import load_dataset

def count_code_lines(code):
    """Count non-empty, non-comment, non-docstring lines."""
    in_docstring = False
    count = 0
    for line in code.split("\n"):
        stripped = line.strip()
        if stripped.startswith('"""') or stripped.startswith("'''"):
            if in_docstring:
                in_docstring = False
                continue
            if stripped.count('"""') >= 2 or stripped.count("'''") >= 2:
                continue  # single-line docstring
            in_docstring = True
            continue
        if in_docstring:
            continue
        if not stripped or stripped.startswith("#"):
            continue
        count += 1
    return count


def classify_quirk(code, name, doc):
    """Classify likely quirk type based on code patterns."""
    code_lower = code.lower()
    doc_lower = (doc or "").lower()
    combined = code_lower + " " + doc_lower

    # A5: accumulation over sequence (sum, prefix, running total, build list)
    if re.search(r'(sum|total|accum|running|prefix|cumul)', combined):
        return "A5-combined"
    if re.search(r'\w+\s*\+=\s*\w+', code) and re.search(r'for\s+\w+\s+in\s+', code):
        return "A5-combined"
    if re.search(r'\.append\(', code) and re.search(r'for\s+\w+\s+in', code):
        return "A4-append-empty"

    # B2: search/find/lookup
    if re.search(r'(find|search|index|contain|lookup|locate)', combined):
        return "B2-trigger-existential"
    if re.search(r'if\s+\w+\s*==\s*\w+.*:\s*\n\s*return', code):
        return "B2-trigger-existential"

    # B1: predicate/validation check
    if re.search(r'(is_valid|is_sorted|all\(|any\(|check|valid|verify|satisf)', combined):
        return "B1-trigger-forall"
    if re.search(r'(sorted|ascending|descending|monoton|order)', combined):
        return "B1-trigger-forall"

    # C1: nonlinear arithmetic
    if re.search(r'[a-z_]\w*\s*\*\s*[a-z_]\w*', code) and \
       re.search(r'(area|volume|product|multiply|scale|factor)', combined):
        return "C1-nla"

    # D: conditional/case analysis
    if code.count("if ") + code.count("elif ") >= 3:
        return "D-case-split"

    # A5 catch-all: any loop building a result
    if re.search(r'result\s*=|output\s*=|ret\s*=', code) and re.search(r'for|while', code):
        return "A5-combined"

    return "unknown"


def is_translatable(code, name):
    """Check if function is reasonably translatable to Dafny."""
    # No imports
    if "import " in code:
        return False

    # Not too much self usage (class methods are OK if simple)
    if code.count("self.") > 3:
        return False

    # No complex Python features
    bad_patterns = [
        r'yield\b', r'async\b', r'await\b', r'lambda\b',
        r'__\w+__', r'@\w+', r'try:', r'except\b',
        r'open\(', r'print\(', r'input\(',
        r'\.read\(', r'\.write\(', r'\.close\(',
        r'subprocess', r'threading', r'socket',
        r'requests\.', r'urllib\.',
    ]
    for pat in bad_patterns:
        if re.search(pat, code):
            return False

    # Should work with basic types
    has_basic = re.search(r'(list|array|int|str|float|len\(|range\(|append|\.sort|sorted)', code)
    if not has_basic:
        return False

    return True


def extract_gist(code, name, doc):
    """Extract a one-line description of the algorithmic gist."""
    # Use the first line of docstring
    if doc:
        first_line = doc.strip().split("\n")[0].strip()
        # Clean up common patterns
        first_line = re.sub(r'^(Returns?|Gets?|Finds?|Computes?|Calculates?)\s+', '', first_line, flags=re.I)
        if len(first_line) > 10:
            return first_line[:150]

    # Fall back to function name
    return name.replace("_", " ")


def main():
    print("Loading CodeSearchNet Python dataset (streaming)...")
    ds = load_dataset("code_search_net", "python", split="train", streaming=True)

    candidates = []
    by_quirk = defaultdict(list)
    target_per_quirk = {
        "A5-combined": 25,
        "A4-append-empty": 15,
        "B2-trigger-existential": 20,
        "B1-trigger-forall": 15,
        "C1-nla": 10,
        "D-case-split": 15,
    }
    total_target = 100

    scanned = 0
    for example in ds:
        scanned += 1
        if scanned > 200000:  # scan up to 200K
            break
        if len(candidates) >= total_target * 2:  # collect extra for diversity
            break

        code = example["func_code_string"]
        name = example["func_name"]
        doc = example["func_documentation_string"]

        # Basic filters
        n_lines = count_code_lines(code)
        if n_lines < 5 or n_lines > 25:
            continue

        if not re.search(r'\b(for|while)\b', code):
            continue

        if not is_translatable(code, name):
            continue

        quirk = classify_quirk(code, name, doc)
        if quirk == "unknown":
            continue

        # Check quota
        if len(by_quirk[quirk]) >= target_per_quirk.get(quirk, 20) * 3:
            continue  # already have enough of this type

        gist = extract_gist(code, name, doc)

        candidate = {
            "id": len(candidates),
            "repo": example["repository_name"],
            "path": example["func_path_in_repository"],
            "name": name,
            "lines": n_lines,
            "quirk_type": quirk,
            "gist": gist,
            "doc": (doc or "")[:300],
            "code": code,
            "url": example.get("func_code_url", ""),
        }

        candidates.append(candidate)
        by_quirk[quirk].append(candidate)

        if scanned % 10000 == 0:
            print(f"  Scanned {scanned}, found {len(candidates)} candidates so far...")

    print(f"\nScanned {scanned} functions total")
    print(f"Raw candidates: {len(candidates)}")
    print(f"By type: {', '.join(f'{k}: {len(v)}' for k, v in sorted(by_quirk.items()))}")

    # Select final 100 with diversity
    selected = []
    for quirk, target in target_per_quirk.items():
        pool = by_quirk.get(quirk, [])
        # Prefer diverse repos
        seen_repos = set()
        diverse = []
        for c in pool:
            if c["repo"] not in seen_repos:
                diverse.append(c)
                seen_repos.add(c["repo"])
        # Fill with duplicates if needed
        diverse.extend([c for c in pool if c not in diverse])
        selected.extend(diverse[:target])

    # Re-number
    for i, c in enumerate(selected):
        c["id"] = i

    print(f"\nSelected {len(selected)} candidates")
    print(f"Final by type: {Counter(c['quirk_type'] for c in selected)}")

    # Save
    out_path = "/Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/real_world/candidates.json"
    with open(out_path, "w") as f:
        json.dump(selected, f, indent=2)
    print(f"Saved to {out_path}")

    # Print sample
    for c in selected[:5]:
        print(f"\n--- {c['id']}: {c['repo']}/{c['name']} ({c['quirk_type']}) ---")
        print(f"  Gist: {c['gist']}")
        print(f"  Code: {c['code'][:200]}...")


if __name__ == "__main__":
    main()

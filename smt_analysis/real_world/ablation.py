#!/usr/bin/env python3
"""Run ablation on real-world Dafny programs to find essential assertions.

For each program, removes assertions one by one and checks if verification
still passes. Reports which assertions are essential (SMT quirks).
"""
from __future__ import annotations

import json
import os
import re
import subprocess
import sys
from pathlib import Path

PROGRAMS_DIR = Path(__file__).parent / "programs"
DOTNET = os.environ.get("DOTNET8",
    "/opt/homebrew/Cellar/dotnet@8/8.0.124/libexec/dotnet")
DAFNY_DLL = os.environ.get("DAFNY_DLL",
    str(Path(__file__).parent.parent.parent / "dafny-source" / "Binaries" / "Dafny.dll"))
VERIFY_TIMEOUT = 30


def verify(code: str, tmp_path: Path) -> bool:
    tmp_path.write_text(code)
    cmd = [DOTNET, DAFNY_DLL, "verify", str(tmp_path),
           "--verification-time-limit", str(VERIFY_TIMEOUT)]
    try:
        r = subprocess.run(cmd, capture_output=True, text=True, timeout=VERIFY_TIMEOUT + 30)
        return "0 errors" in r.stdout
    except:
        return False


def find_assertions(code: str) -> list[dict]:
    """Find all assert statements with their line numbers."""
    asserts = []
    lines = code.split("\n")
    for i, line in enumerate(lines):
        stripped = line.strip()
        if stripped.startswith("assert ") and ";" in stripped:
            # Check if it has a quirk comment
            quirk_comment = ""
            if "//" in stripped:
                quirk_comment = stripped[stripped.index("//"):].strip()
            elif i + 1 < len(lines) and "//" in lines[i].split("//", 1)[-1] if "//" in lines[i] else "":
                pass
            # Check previous line for comment
            if i > 0 and lines[i-1].strip().startswith("//"):
                quirk_comment = lines[i-1].strip()

            asserts.append({
                "line": i + 1,
                "text": stripped,
                "quirk_comment": quirk_comment,
            })
    return asserts


def remove_assertion(code: str, line_num: int) -> str:
    """Comment out a single assertion by line number."""
    lines = code.split("\n")
    idx = line_num - 1
    lines[idx] = "// REMOVED: " + lines[idx].strip()
    return "\n".join(lines)


def main():
    tmp = PROGRAMS_DIR / "tmp_ablation.dfy"
    results = []

    for dfy_path in sorted(PROGRAMS_DIR.glob("*.dfy")):
        name = dfy_path.stem
        code = dfy_path.read_text()
        asserts = find_assertions(code)

        if not asserts:
            print(f"{name}: no assertions found")
            continue

        print(f"\n{name}: {len(asserts)} assertions")

        essential = []
        non_essential = []

        for a in asserts:
            stripped_code = remove_assertion(code, a["line"])
            ok = verify(stripped_code, tmp)
            status = "non-essential" if ok else "ESSENTIAL"
            print(f"  L{a['line']}: {status} — {a['text'][:70]}")

            if not ok:
                essential.append(a)
            else:
                non_essential.append(a)

        results.append({
            "file": name,
            "total_assertions": len(asserts),
            "essential": len(essential),
            "non_essential": len(non_essential),
            "essential_assertions": essential,
            "non_essential_assertions": non_essential,
        })

    # Summary
    print(f"\n{'='*60}")
    print(f"ABLATION SUMMARY")
    print(f"{'='*60}")

    total_essential = 0
    total_assertions = 0
    for r in results:
        total_essential += r["essential"]
        total_assertions += r["total_assertions"]
        ess = r["essential"]
        tot = r["total_assertions"]
        print(f"  {r['file']}: {ess}/{tot} essential")
        for a in r["essential_assertions"]:
            print(f"    L{a['line']}: {a['text'][:80]}")

    print(f"\nTotal: {total_essential}/{total_assertions} essential assertions across {len(results)} programs")

    # Save results
    out_path = PROGRAMS_DIR.parent / "ablation_results.json"
    out_path.write_text(json.dumps(results, indent=2))
    print(f"Saved to {out_path}")

    # Clean up
    tmp.unlink(missing_ok=True)


if __name__ == "__main__":
    main()

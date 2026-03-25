#!/usr/bin/env python3
"""Run verus verification on all translated programs.

Reports which programs verify, which fail, and which timeout.
This tests that the spec + implementation are consistent.

Usage:
    python3 verify_all.py                # verify all translated programs
    python3 verify_all.py --problem X    # verify specific problem
"""
from __future__ import annotations

import argparse
import json
import subprocess
import time
from pathlib import Path

SCRIPT_DIR = Path(__file__).parent.resolve()
PROGRAMS_DIR = SCRIPT_DIR / "programs"
STATUS_FILE = SCRIPT_DIR / "status.json"
VERUS_BIN = "/tmp/verus_install/verus-arm64-macos/verus"
TIMEOUT = 60  # seconds per program


def verify_one(rs_path: Path) -> dict:
    """Run verus on a single file. Returns {result, time, errors}."""
    t0 = time.time()
    try:
        r = subprocess.run(
            [VERUS_BIN, str(rs_path)],
            capture_output=True, text=True, timeout=TIMEOUT
        )
        output = r.stdout + "\n" + r.stderr
        elapsed = round(time.time() - t0, 2)

        if r.returncode == 0 and "0 errors" in output:
            return {"result": "verified", "time": elapsed}
        elif "timed out" in output.lower() or "timeout" in output.lower():
            return {"result": "timeout", "time": elapsed, "errors": output[:500]}
        else:
            # Extract error lines
            errors = [l.strip() for l in output.split("\n")
                      if "error" in l.lower() and not l.strip().startswith("//")]
            return {"result": "failed", "time": elapsed,
                    "errors": "\n".join(errors[:10]) if errors else output[:500]}
    except subprocess.TimeoutExpired:
        return {"result": "timeout", "time": TIMEOUT}
    except FileNotFoundError:
        return {"result": "error", "error": "verus binary not found"}


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--problem", nargs="+", help="Specific problems")
    parser.add_argument("--timeout", type=int, default=60)
    args = parser.parse_args()

    global TIMEOUT
    TIMEOUT = args.timeout

    status = json.loads(STATUS_FILE.read_text())
    translated = sorted(status["translated"].keys())

    if args.problem:
        translated = [p for p in args.problem if p in status["translated"]]

    print(f"Verifying {len(translated)} translated programs (timeout={TIMEOUT}s)...")

    results = {}
    verified = 0
    failed = 0
    timed_out = 0

    for i, problem in enumerate(translated):
        rs_path = PROGRAMS_DIR / problem / "translated.rs"
        if not rs_path.exists():
            print(f"  [{i+1}/{len(translated)}] {problem}: SKIP (no translated.rs)")
            continue

        r = verify_one(rs_path)
        results[problem] = r

        if r["result"] == "verified":
            verified += 1
            print(f"  [{i+1}/{len(translated)}] {problem}: VERIFIED ({r['time']}s)")
        elif r["result"] == "timeout":
            timed_out += 1
            print(f"  [{i+1}/{len(translated)}] {problem}: TIMEOUT")
        else:
            failed += 1
            err_preview = r.get("errors", "")[:100]
            print(f"  [{i+1}/{len(translated)}] {problem}: FAILED — {err_preview}")

    print(f"\n{'='*60}")
    print(f"VERIFICATION SUMMARY")
    print(f"{'='*60}")
    print(f"Verified: {verified}")
    print(f"Failed:   {failed}")
    print(f"Timeout:  {timed_out}")
    print(f"Total:    {len(results)}")

    # Save results
    out = SCRIPT_DIR / "verification_results.json"
    out.write_text(json.dumps({
        "verified": verified, "failed": failed, "timeout": timed_out,
        "total": len(results), "per_problem": results,
    }, indent=2))
    print(f"Saved to {out}")


if __name__ == "__main__":
    main()

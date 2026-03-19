#!/usr/bin/env python3
"""Re-run only the prover_error variants using stock dafny verify."""

import json
import subprocess
import time
from pathlib import Path

RESULTS_DIR = Path(__file__).parent.parent / "smt_analysis" / "results"


def run_stock_dafny(variant_path: Path, timeout: int = 60) -> str:
    """Run stock dafny verify, return 'pass', 'error', 'timeout', or 'parse_error'."""
    try:
        r = subprocess.run(
            ["dafny", "verify", str(variant_path),
             "--verification-time-limit", str(timeout)],
            capture_output=True, text=True, timeout=timeout + 60,
        )
        output = r.stdout + r.stderr
        if "parse error" in output.lower() or "not expected in Dafny" in output:
            return "parse_error"
        if "0 errors" in output:
            return "pass"
        if "timed out" in output:
            return "timeout"
        return "error"
    except subprocess.TimeoutExpired:
        return "timeout"


def main():
    total_rerun = 0
    total_essential = 0
    total_redundant = 0
    problem_essentials = {}

    for d in sorted(RESULTS_DIR.iterdir()):
        rfile = d / "ablation_rerun" / "results.json"
        if not rfile.exists():
            continue

        data = json.load(open(rfile))
        prover_errors = [r for r in data.get("results", []) if r.get("ablation_result") == "prover_error"]
        if not prover_errors:
            continue

        print(f"\n{d.name}: {len(prover_errors)} prover_error variants to re-check")
        essentials = []

        for r in prover_errors:
            variant_path = d / "ablation_rerun" / f"without_{r['index']:02d}.dfy"
            if not variant_path.exists():
                print(f"  [{r['index']:02d}] MISSING variant file")
                continue

            t0 = time.time()
            result = run_stock_dafny(variant_path)
            elapsed = time.time() - t0
            total_rerun += 1

            # Update the result in-place
            r["ablation_result"] = result
            r["ablation_time"] = round(elapsed, 2)
            r["essential"] = result in ("error", "timeout")

            if r["essential"]:
                total_essential += 1
                essentials.append(r)
                print(f"  [{r['index']:02d}] line {r['line']}: ESSENTIAL ({result}, {elapsed:.1f}s) {r['text'][:70]}")
            else:
                total_redundant += 1
                print(f"  [{r['index']:02d}] line {r['line']}: redundant ({result}, {elapsed:.1f}s)")

        # Save updated results
        rfile.write_text(json.dumps(data, indent=2))

        if essentials:
            problem_essentials[d.name] = essentials

    print(f"\n=== RERUN TOTALS ===")
    print(f"Re-checked: {total_rerun}")
    print(f"Essential: {total_essential}")
    print(f"Redundant: {total_redundant}")
    print(f"Problems with essential: {len(problem_essentials)}")
    for prob, ess in problem_essentials.items():
        print(f"  {prob}: {len(ess)} essential")
        for e in ess:
            print(f"    line {e['line']}: {e['text'][:90]}")


if __name__ == "__main__":
    main()

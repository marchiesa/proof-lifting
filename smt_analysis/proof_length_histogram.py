#!/usr/bin/env python3
"""
Plot histograms of proof length (assertions + invariants) split by
stability under seed variation (from seed_variation_1s.json).

Usage:
    python3 smt_analysis/proof_length_histogram.py
"""

import json
import re
from pathlib import Path

import matplotlib.pyplot as plt
import numpy as np

PROJ_ROOT = Path(__file__).parent.parent.resolve()
RESULTS_DIR = PROJ_ROOT / "smt_analysis" / "results"


def extract_scopes(src: str) -> list[dict]:
    """Extract method/lemma scopes using brace matching.
    Returns list of {name, kind, start_line, end_line, body}."""
    lines = src.splitlines()
    scopes = []

    decl_re = re.compile(r'^\s*(method|lemma)\s+(\w+)', re.MULTILINE)
    for m in decl_re.finditer(src):
        kind = m.group(1)
        name = m.group(2)
        start_line = src[:m.start()].count('\n')  # 0-indexed

        # Find opening brace of the body (skip signature lines)
        depth = 0
        body_start = None
        for i, line in enumerate(lines[start_line:], start=start_line):
            for ch in line:
                if ch == '{':
                    if depth == 0:
                        body_start = i
                    depth += 1
                elif ch == '}':
                    depth -= 1
                    if depth == 0 and body_start is not None:
                        scopes.append({
                            "name": name, "kind": kind,
                            "start_line": start_line, "end_line": i,
                            "body_lines": lines[body_start:i+1],
                        })
                        break
            if depth == 0 and body_start is not None:
                break

    return scopes


def strip_block_comments(src: str) -> str:
    return re.sub(r'/\*.*?\*/', '', src, flags=re.DOTALL)


def count_proof_annotations(dfy_path: Path) -> dict:
    src = strip_block_comments(dfy_path.read_text())
    scopes = extract_scopes(src)

    per_scope = []
    for s in scopes:
        body = "\n".join(s["body_lines"])
        loc        = sum(1 for l in s["body_lines"] if l.strip() and not l.strip().startswith("//"))
        asserts    = len(re.findall(r'^\s*assert\b',    body, re.MULTILINE))
        invariants = len(re.findall(r'^\s*invariant\b', body, re.MULTILINE))
        per_scope.append({
            "name": s["name"], "kind": s["kind"],
            "loc": loc, "asserts": asserts, "invariants": invariants,
            "total_annotations": asserts + invariants,
        })

    total_loc   = sum(s["loc"] for s in per_scope)
    max_loc     = max((s["loc"] for s in per_scope), default=0)
    total_annot = sum(s["total_annotations"] for s in per_scope)
    return {
        "per_scope": per_scope,
        "total_loc": total_loc,
        "max_scope_loc": max_loc,
        "total_annotations": total_annot,
        "n_scopes": len(per_scope),
    }


def main():
    seed_data = json.loads((RESULTS_DIR / "seed_variation_1s.json").read_text())

    # {metric_key: (stable_vals, unstable_vals)}
    data = {"total_loc": ([], []), "max_scope_loc": ([], []), "total_annotations": ([], []), "max_scope_annotations": ([], [])}

    for r in seed_data["results"]:
        name = r["problem"]
        dfy = RESULTS_DIR / name / "verified.dfy"
        if not dfy.exists():
            print(f"  WARNING: {name}/verified.dfy not found, skipping")
            continue
        counts = count_proof_annotations(dfy)
        tag = "UNSTABLE" if r["brittle"] else "stable  "
        scopes_str = ", ".join(f"{s['kind']} {s['name']}({s['loc']})" for s in counts["per_scope"])
        print(f"  {tag}  {name:25s}  total={counts['total_loc']:4d}  max={counts['max_scope_loc']:4d}  annot={counts['total_annotations']:3d}  [{scopes_str}]")
        bucket = 1 if r["brittle"] else 0
        max_scope_annot = max((s["total_annotations"] for s in counts["per_scope"]), default=0)
        data["total_loc"][bucket].append(counts["total_loc"])
        data["max_scope_loc"][bucket].append(counts["max_scope_loc"])
        data["total_annotations"][bucket].append(counts["total_annotations"])
        data["max_scope_annotations"][bucket].append(max_scope_annot)

    print()
    for metric, (sv, uv) in data.items():
        print(f"{metric}:")
        print(f"  Stable   n={len(sv):2d}  mean={np.mean(sv):.1f}  median={np.median(sv):.1f}  max={max(sv)}")
        print(f"  Unstable n={len(uv):2d}  mean={np.mean(uv):.1f}  median={np.median(uv):.1f}  max={max(uv) if uv else 'N/A'}")
    print()

    def plot_figure(metrics, titles, xlabels, suptitle, out_path, bins_step=10):
        fig, axes = plt.subplots(2, 2, figsize=(11, 8))
        fig.suptitle(suptitle, fontsize=13)
        for row, metric in enumerate(metrics):
            sv, uv = data[metric]
            all_vals = sv + uv
            bin_max = max(all_vals) + 5
            bins = np.arange(0, bin_max + bins_step, bins_step)
            for col, (lengths, label, color) in enumerate([
                (sv, f"Stable  (n={len(sv)})",   "#4c9be8"),
                (uv, f"Unstable (n={len(uv)})",  "#e8694c"),
            ]):
                ax = axes[row][col]
                ax.hist(lengths, bins=bins, color=color, edgecolor="white", linewidth=0.6)
                ax.set_title(f"{titles[metric]} — {label}", fontsize=10)
                ax.set_xlabel(xlabels[metric])
                ax.set_ylabel("# problems")
                ax.set_xlim(0, bin_max)
                if lengths:
                    ax.axvline(np.mean(lengths),   color="black", linestyle="--", linewidth=1.2, label=f"mean={np.mean(lengths):.1f}")
                    ax.axvline(np.median(lengths), color="grey",  linestyle=":",  linewidth=1.2, label=f"median={np.median(lengths):.1f}")
                    ax.legend(fontsize=9)
        plt.tight_layout()
        plt.savefig(out_path, dpi=150, bbox_inches="tight")
        print(f"Saved to {out_path}")

    plot_figure(
        metrics=["total_loc", "max_scope_loc"],
        titles={"total_loc": "Total LOC across all scopes", "max_scope_loc": "Max LOC of any single scope"},
        xlabels={"total_loc": "total lines of code", "max_scope_loc": "lines of code (largest scope)"},
        suptitle="LOC per proof scope by seed-stability (1s limit)",
        out_path=PROJ_ROOT / "smt_analysis" / "results" / "loc_histogram.png",
        bins_step=10,
    )

    plot_figure(
        metrics=["total_annotations", "max_scope_annotations"],
        titles={"total_annotations": "Total assertions + invariants", "max_scope_annotations": "Max assertions + invariants of any single scope"},
        xlabels={"total_annotations": "assertions + invariants", "max_scope_annotations": "assertions + invariants (largest scope)"},
        suptitle="Proof annotations by seed-stability (1s limit)",
        out_path=PROJ_ROOT / "smt_analysis" / "results" / "annotations_histogram.png",
        bins_step=1,
    )


if __name__ == "__main__":
    main()

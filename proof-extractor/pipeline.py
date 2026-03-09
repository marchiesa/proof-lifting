#!/usr/bin/env python3
"""
Complete proof extraction pipeline using MODIFIED Boogie.

Pipeline:
1. Dafny → Boogie + AST mapping (--ast-mapping, --bprint)
2. Modified Boogie → SMT + nameMap (/proverLog, /nameMap)
3. Z3 → unsat core
4. Map core back via nameMap → Boogie → Dafny
5. Build DAG → topological order
6. Generate Dafny assertions with ghost vars for unmapped terms
"""

import argparse
import json
import os
import subprocess
import tempfile
from pathlib import Path

from core_to_proof import CoreToProof


class Pipeline:
    """Full pipeline using modified Boogie."""

    def __init__(self):
        self.base_dir = Path(__file__).parent.parent
        self.dafny_source = self.base_dir / "dafny-source"
        self.boogie_source = self.base_dir / "boogie"
        self.dotnet = "/opt/homebrew/opt/dotnet@8/bin/dotnet"

    def run_dafny(self, dfy_file: str, output_dir: str) -> tuple[str, str]:
        """Run Dafny to get AST mapping and Boogie file."""
        dfy_file = os.path.abspath(dfy_file)
        ast_mapping = os.path.join(output_dir, "ast_mapping.json")
        boogie_file = os.path.join(output_dir, "output.bpl")

        cmd = [
            self.dotnet, "run",
            "--project", str(self.dafny_source / "Source/DafnyDriver/DafnyDriver.csproj"),
            "--", "verify", dfy_file,
            "--ast-mapping", ast_mapping,
            "--bprint", boogie_file,
        ]

        result = subprocess.run(
            cmd, capture_output=True, text=True,
            cwd=str(self.dafny_source), timeout=300
        )

        if not os.path.exists(ast_mapping):
            raise RuntimeError(f"AST mapping not generated: {result.stderr[:500]}")

        return ast_mapping, boogie_file

    def run_modified_boogie(self, boogie_file: str, output_dir: str) -> tuple[str, str]:
        """Run MODIFIED Boogie to get SMT + nameMap."""
        smt_file = os.path.join(output_dir, "output.smt2")
        name_map = os.path.join(output_dir, "name_map.json")

        cmd = [
            self.dotnet, "run",
            "--project", str(self.boogie_source / "Source/BoogieDriver/BoogieDriver.csproj"),
            "--", boogie_file,
            f"/proverLog:{smt_file}",
            f"/nameMap:{name_map}",
            "/trackVerificationCoverage",  # REQUIRED for :named assertions in SMT
            "/normalizeNames:1",  # REQUIRED for $generated@@N → Boogie name mapping
        ]

        result = subprocess.run(
            cmd, capture_output=True, text=True, timeout=300
        )

        if not os.path.exists(name_map):
            raise RuntimeError(f"nameMap not generated: {result.stderr[:500]}")

        return smt_file, name_map

    def map_core_to_dafny(self, core: list, ast_mapping: dict, name_map: dict) -> list:
        """Map unsat core assertion IDs back to Dafny expressions via AST mapping."""
        proof_lines = []

        # Build ID → Dafny text mapping from AST
        id_to_dafny = {}

        for method in ast_mapping.get('methods', []):
            # Map invariants
            for inv in method.get('invariants', []):
                boogie_id = inv.get('boogieId', '')
                text = inv.get('text', '')
                if boogie_id and text:
                    id_to_dafny[f"{boogie_id}$maintained"] = f"// Invariant maintained: {text}"
                    id_to_dafny[f"{boogie_id}$established"] = f"// Invariant established: {text}"
                    id_to_dafny[f"{boogie_id}$assume_in_body"] = f"// Invariant assumed: {text}"
                    id_to_dafny[boogie_id] = text

            # Map assertions
            for asrt in method.get('assertions', []):
                boogie_id = asrt.get('boogieId', '')
                text = asrt.get('text', '')
                if boogie_id and text:
                    id_to_dafny[boogie_id] = text

            # Map requires
            for req in method.get('requires', []):
                boogie_id = req.get('boogieId', '')
                text = req.get('text', '')
                if boogie_id and text:
                    id_to_dafny[boogie_id] = f"// Requires: {text}"

            # Map ensures (appears as assert$$idN in core)
            for ens in method.get('ensures', []):
                boogie_id = ens.get('boogieId', '')
                text = ens.get('text', '')
                if boogie_id and text:
                    id_to_dafny[boogie_id] = f"ensures {text}"

        # Process core assertions
        for core_elem in core:
            # Core elements are like "aux$$assert$$id7$maintained"
            # Extract the ID part
            if core_elem.startswith('aux$$'):
                assertion_name = core_elem[5:]  # Remove "aux$$"
            else:
                assertion_name = core_elem

            # Remove "assert$$" or "assume$$" prefix
            if assertion_name.startswith('assert$$'):
                id_part = assertion_name[8:]  # Remove "assert$$"
                prefix = "assert"
            elif assertion_name.startswith('assume$$'):
                id_part = assertion_name[8:]  # Remove "assume$$"
                prefix = "assume"
            else:
                id_part = assertion_name
                prefix = ""

            # Look up in our mapping
            if id_part in id_to_dafny:
                dafny_text = id_to_dafny[id_part]
                if dafny_text.startswith('//'):
                    proof_lines.append(dafny_text)
                else:
                    proof_lines.append(f"assert {dafny_text};  // {id_part}")
            else:
                # Not in AST mapping - show raw ID
                proof_lines.append(f"// {prefix}: {id_part}")

        return proof_lines

    def process(self, dfy_file: str, output_file: str = None):
        """Run the full pipeline."""
        print(f"Processing: {dfy_file}\n")

        with tempfile.TemporaryDirectory() as tmpdir:
            # Step 1: Dafny → Boogie + AST mapping
            print("[1/4] Dafny → Boogie + AST mapping...")
            ast_mapping_file, boogie_file = self.run_dafny(dfy_file, tmpdir)

            with open(ast_mapping_file) as f:
                ast_mapping = json.load(f)
            print(f"      AST mapping: {len(ast_mapping.get('methods', []))} methods")

            # Step 2: Modified Boogie → SMT + nameMap
            print("[2/4] Modified Boogie → SMT + nameMap...")
            smt_file, name_map_file = self.run_modified_boogie(boogie_file, tmpdir)

            with open(name_map_file) as f:
                name_map = json.load(f)
            print(f"      nameMap: {len(name_map.get('variables', {}))} vars, {len(name_map.get('assertions', {}))} assertions")

            # Step 3: Z3 → unsat core + DAG + mapping
            print("[3/4] Z3 → unsat core → DAG → Dafny...")
            converter = CoreToProof(smt_file, ast_mapping, name_map)
            converter.extract_named_assertions()
            print(f"      Found {len(converter.assertions)} named assertions in SMT")

            core = converter.get_unsat_core()
            print(f"      Unsat core: {len(core)} assertions")

            # Step 4: Generate ordered proof using full SMT translation
            print("[4/4] Building DAG and translating to Dafny...")

            # Use the full build_proof which:
            # 1. Builds dependency DAG from SMT expressions
            # 2. Topologically sorts for ordering
            # 3. Translates each SMT expr to Dafny via mapping chain
            # 4. Creates ghost vars for unmapped Z3 terms
            proof_lines = converter.build_proof(core)

            # Also show which assertions mapped via ID lookup
            id_mapped = self.map_core_to_dafny(core, ast_mapping, name_map)

            print(f"      Generated {len(proof_lines)} proof assertions")
            print(f"      ID-mapped {len(id_mapped)} assertions")

            # Output both versions
            output = "// === Proof from SMT translation ===\n"
            output += '\n'.join(proof_lines)
            output += "\n\n// === Assertions from ID lookup ===\n"
            output += '\n'.join(id_mapped)

            if output_file:
                with open(output_file, 'w') as f:
                    f.write(output)
                print(f"\nOutput: {output_file}")
            else:
                print("\n=== Generated Proof ===")
                print(output)

            return proof_lines


def main():
    parser = argparse.ArgumentParser(description="Extract proof from Dafny via modified Boogie")
    parser.add_argument('input', help='Input Dafny file')
    parser.add_argument('-o', '--output', help='Output file')
    args = parser.parse_args()

    pipeline = Pipeline()
    pipeline.process(args.input, args.output)


if __name__ == "__main__":
    main()

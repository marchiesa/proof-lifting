#!/bin/bash
# Run modified Dafny verify with full AST mapping + SMT logging.
#
# Usage: bash run_dafny_verify.sh <dfy_file> <output_dir> [timeout_seconds]
#
# Produces in output_dir/:
#   ast_mapping.json  — Dafny->Boogie mapping (from modified Dafny)
#   output.bpl        — Boogie IL
#   output.smt2       — SMT-LIB sent to Z3 (from modified Boogie)
#   name_map.json     — Boogie->SMT per-VC mapping (from modified Boogie)
#   dafny_output.txt  — Dafny verify stdout/stderr
#
# Exit code: 0 if verification passes, 1 if it fails, 2 if error.

set -euo pipefail

DFY_FILE="$1"
OUTPUT_DIR="$2"
TIMEOUT="${3:-60}"

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
BASE_DIR="$(cd "$SCRIPT_DIR/../.." && pwd)"
DOTNET="${DOTNET8:-${DOTNET:-dotnet}}"
DAFNY_DLL="$BASE_DIR/dafny-source/Binaries/Dafny.dll"
BOOGIE_PROJ="$BASE_DIR/boogie/Source/BoogieDriver/BoogieDriver.csproj"

mkdir -p "$OUTPUT_DIR"

AST_MAPPING="$OUTPUT_DIR/ast_mapping.json"
BOOGIE_FILE="$OUTPUT_DIR/output.bpl"
SMT_FILE="$OUTPUT_DIR/output.smt2"
NAME_MAP="$OUTPUT_DIR/name_map.json"
DAFNY_OUTPUT="$OUTPUT_DIR/dafny_output.txt"

# Step 1: Run modified Dafny to produce AST mapping + Boogie IL
echo "[run_dafny_verify] Step 1: Dafny verify + AST mapping..."
DAFNY_EXIT=0
"$DOTNET" "$DAFNY_DLL" verify "$DFY_FILE" \
    --ast-mapping "$AST_MAPPING" \
    --bprint "$BOOGIE_FILE" \
    --verification-time-limit "$TIMEOUT" \
    > "$DAFNY_OUTPUT" 2>&1 || DAFNY_EXIT=$?

echo "[run_dafny_verify] Dafny exit code: $DAFNY_EXIT"

# Check if Boogie file was produced (needed for step 2)
if [ ! -f "$BOOGIE_FILE" ]; then
    echo "[run_dafny_verify] ERROR: Boogie file not produced"
    cat "$DAFNY_OUTPUT"
    exit 2
fi

# Step 2: Run modified Boogie to produce SMT log + name map
echo "[run_dafny_verify] Step 2: Modified Boogie -> SMT + name map..."
BOOGIE_EXIT=0
"$DOTNET" run --project "$BOOGIE_PROJ" -- "$BOOGIE_FILE" \
    "/proverLog:$SMT_FILE" \
    "/nameMap:$NAME_MAP" \
    /trackVerificationCoverage \
    "/normalizeNames:1" \
    "/timeLimit:$TIMEOUT" \
    > "$OUTPUT_DIR/boogie_output.txt" 2>&1 || BOOGIE_EXIT=$?

echo "[run_dafny_verify] Boogie exit code: $BOOGIE_EXIT"

# Report what was produced
echo "[run_dafny_verify] Artifacts:"
for f in "$AST_MAPPING" "$BOOGIE_FILE" "$SMT_FILE" "$NAME_MAP"; do
    if [ -f "$f" ]; then
        SIZE=$(wc -c < "$f" | tr -d ' ')
        echo "  $(basename "$f"): ${SIZE} bytes"
    else
        echo "  $(basename "$f"): MISSING"
    fi
done

# Exit with Dafny's exit code (0 = verified, non-0 = failed)
exit $DAFNY_EXIT

#!/bin/bash
# Test a proposed Boogie axiom by patching a BPL file and running Boogie.
#
# Usage: bash test_axiom.sh <bpl_file> <axiom_file> [timeout_seconds]
#
# The axiom_file should contain one or more Boogie axioms.
# They are inserted after the first "// END PRELUDE" or "axiom" line in the BPL.
#
# Output: JSON to stdout with {result, exit_code, errors, time_seconds}

set -uo pipefail

BPL_FILE="$1"
AXIOM_FILE="$2"
TIMEOUT="${3:-60}"

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
BASE_DIR="$(cd "$SCRIPT_DIR/../.." && pwd)"
DOTNET="${DOTNET8:-${DOTNET:-dotnet}}"
BOOGIE_PROJ="$BASE_DIR/boogie/Source/BoogieDriver/BoogieDriver.csproj"

# Create patched BPL in a temp file
PATCHED_BPL=$(mktemp /tmp/patched_XXXXXX.bpl)
TMPOUT=$(mktemp)

# Insert axiom after the last top-level axiom in the preamble (before first procedure)
python3 - "$BPL_FILE" "$AXIOM_FILE" "$PATCHED_BPL" <<'PYEOF'
import sys, re

bpl_file, axiom_file, output_file = sys.argv[1:4]

with open(bpl_file) as f:
    bpl = f.read()
with open(axiom_file) as f:
    axiom = f.read()

# Find insertion point: just before the first "procedure" or "implementation" line
lines = bpl.split("\n")
insert_at = 0
for i, line in enumerate(lines):
    stripped = line.strip()
    if stripped.startswith("procedure ") or stripped.startswith("implementation "):
        insert_at = i
        break
    # Track last axiom line as fallback
    if stripped.startswith("axiom "):
        insert_at = i + 1

# Insert the axiom
patched_lines = lines[:insert_at] + [
    "",
    "// === PROPOSED AXIOM (test_axiom.sh) ===",
    axiom.rstrip(),
    "// === END PROPOSED AXIOM ===",
    "",
] + lines[insert_at:]

with open(output_file, "w") as f:
    f.write("\n".join(patched_lines))

print(f"Inserted axiom at line {insert_at}", file=sys.stderr)
PYEOF

START_TIME=$(python3 -c "import time; print(time.time())")

# Run Boogie on patched BPL
"$DOTNET" run --project "$BOOGIE_PROJ" -- "$PATCHED_BPL" \
    /trackVerificationCoverage \
    "/normalizeNames:1" \
    "/timeLimit:$TIMEOUT" \
    > "$TMPOUT" 2>&1 || true
EXIT_CODE=$?

END_TIME=$(python3 -c "import time; print(time.time())")

# Produce JSON output
python3 - "$TMPOUT" "$EXIT_CODE" "$START_TIME" "$END_TIME" "$PATCHED_BPL" <<'PYEOF'
import sys, json

output_file, exit_code_str, start_str, end_str, patched_bpl = sys.argv[1:6]
exit_code = int(exit_code_str)
elapsed = round(float(end_str) - float(start_str), 2)

with open(output_file) as f:
    raw_output = f.read()

# Determine result
if "0 errors" in raw_output:
    result = "pass"
elif "timed out" in raw_output.lower():
    result = "timeout"
else:
    result = "error"

# Extract error/verification lines
errors = []
verified_count = 0
error_count = 0
for line in raw_output.split("\n"):
    line = line.strip()
    if not line:
        continue
    if "verified" in line.lower() and "error" in line.lower():
        import re
        m = re.search(r'(\d+)\s+verified,\s+(\d+)\s+error', line)
        if m:
            verified_count = int(m.group(1))
            error_count = int(m.group(2))
    if "Error" in line or "error" in line or "could not be proved" in line:
        errors.append(line)
        if len(errors) >= 10:
            break

print(json.dumps({
    "result": result,
    "exit_code": exit_code,
    "verified_count": verified_count,
    "error_count": error_count,
    "errors": errors,
    "time_seconds": elapsed,
    "patched_bpl": patched_bpl,
    "raw_output": raw_output[:5000],
}, indent=2))
PYEOF

rm -f "$TMPOUT"
# Keep patched BPL for debugging (caller can delete it)

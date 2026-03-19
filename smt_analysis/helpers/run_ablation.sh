#!/bin/bash
# Run dafny verify on a variant file (for ablation testing).
# Lighter weight than run_dafny_verify.sh — only runs Dafny, no Boogie/SMT logging.
#
# Usage: bash run_ablation.sh <dfy_file> [timeout_seconds]
#
# Output: JSON to stdout with {result, exit_code, errors, time_seconds}

set -uo pipefail

DFY_FILE="$1"
TIMEOUT="${2:-60}"

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
BASE_DIR="$(cd "$SCRIPT_DIR/../.." && pwd)"
DOTNET="${DOTNET8:-${DOTNET:-dotnet}}"
DAFNY_DLL="$BASE_DIR/dafny-source/Binaries/Dafny.dll"

START_TIME=$(python3 -c "import time; print(time.time())")

TMPOUT=$(mktemp)
"$DOTNET" "$DAFNY_DLL" verify "$DFY_FILE" \
    --verification-time-limit "$TIMEOUT" \
    > "$TMPOUT" 2>&1 || true
EXIT_CODE=$?

END_TIME=$(python3 -c "import time; print(time.time())")

# Use python3 to produce the JSON output — avoids all shell quoting issues
python3 - "$TMPOUT" "$EXIT_CODE" "$START_TIME" "$END_TIME" <<'PYEOF'
import sys, json

output_file, exit_code_str, start_str, end_str = sys.argv[1:5]
exit_code = int(exit_code_str)
elapsed = round(float(end_str) - float(start_str), 2)

with open(output_file) as f:
    raw_output = f.read()

# Determine result
if "0 errors" in raw_output:
    result = "pass"
elif "parse error" in raw_output.lower() or "not expected in Dafny" in raw_output:
    result = "parse_error"
# Note: "Model parsing error" was caused by a locale bug in Boogie's model
# parser (double.TryParse without InvariantCulture). Fixed in our modified
# Boogie; this branch should no longer trigger.
elif "Model parsing error" in raw_output or "Could not parse any models" in raw_output:
    result = "prover_error"
elif "timed out" in raw_output:
    result = "timeout"
else:
    result = "error"

# Extract error lines
errors = []
for line in raw_output.split("\n"):
    line = line.strip()
    if line and ("Error" in line or "error" in line or "could not be proved" in line):
        errors.append(line)
        if len(errors) >= 5:
            break

print(json.dumps({
    "result": result,
    "exit_code": exit_code,
    "errors": errors,
    "time_seconds": elapsed,
    "raw_output": raw_output,
}, indent=2))
PYEOF

rm -f "$TMPOUT"

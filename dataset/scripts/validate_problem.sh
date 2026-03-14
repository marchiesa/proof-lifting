#!/usr/bin/env bash
# Validate a Dafny benchmark problem.
#
# Usage: ./validate_problem.sh <problem_dir>
#
# Checks:
# 1. task.dfy resolves (no parse/type errors) but does NOT verify
# 2. reference.dfy compiles AND verifies (the solution is correct)
# 3. tests.dfy compiles AND verifies (the spec is testable)

set -euo pipefail

DOTNET="/opt/homebrew/Cellar/dotnet@8/8.0.124/libexec/dotnet"
DAFNY_DLL="/Users/mchiesa/work/projects/2026-02-dafny-liftings/dafny-source/Binaries/Dafny.dll"

RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
NC='\033[0m' # No Color

if [ $# -lt 1 ]; then
    echo "Usage: $0 <problem_dir>"
    exit 1
fi

PROBLEM_DIR="$1"

# Strip trailing slash
PROBLEM_DIR="${PROBLEM_DIR%/}"

if [ ! -d "$PROBLEM_DIR" ]; then
    echo -e "${RED}Error: Directory not found: $PROBLEM_DIR${NC}"
    exit 1
fi

PROBLEM_ID=$(basename "$PROBLEM_DIR")
echo "========================================"
echo "Validating: $PROBLEM_ID"
echo "========================================"

ERRORS=0

# Check required files exist
for f in problem.md task.dfy reference.dfy tests.dfy metadata.json; do
    if [ ! -f "$PROBLEM_DIR/$f" ]; then
        echo -e "${RED}MISSING: $f${NC}"
        ERRORS=$((ERRORS + 1))
    fi
done

if [ $ERRORS -gt 0 ]; then
    echo -e "${RED}Cannot validate: missing files${NC}"
    exit 1
fi

# 1. task.dfy should resolve but NOT verify
echo ""
echo "--- Checking task.dfy (should fail verification) ---"
TASK_OUTPUT=$("$DOTNET" "$DAFNY_DLL" verify "$PROBLEM_DIR/task.dfy" 2>&1 || true)
if echo "$TASK_OUTPUT" | grep -q "0 errors"; then
    echo -e "${YELLOW}WARNING: task.dfy verifies successfully -- the task may be trivial${NC}"
    echo "  (Expected verification to fail since invariants are missing)"
    ERRORS=$((ERRORS + 1))
else
    # Check it at least resolves (no parse/type errors)
    RESOLVE_OUTPUT=$("$DOTNET" "$DAFNY_DLL" resolve "$PROBLEM_DIR/task.dfy" 2>&1 || true)
    RESOLVE_EXIT=$?
    if [ $RESOLVE_EXIT -eq 0 ]; then
        echo -e "${GREEN}PASS: task.dfy resolves but fails verification (as expected)${NC}"
    else
        echo -e "${RED}FAIL: task.dfy has parse/type errors:${NC}"
        echo "$RESOLVE_OUTPUT" | head -20
        ERRORS=$((ERRORS + 1))
    fi
fi

# 2. reference.dfy should compile AND verify
echo ""
echo "--- Checking reference.dfy (should verify) ---"
REF_OUTPUT=$("$DOTNET" "$DAFNY_DLL" verify "$PROBLEM_DIR/reference.dfy" 2>&1 || true)
if echo "$REF_OUTPUT" | grep -q "0 errors"; then
    echo -e "${GREEN}PASS: reference.dfy verifies successfully${NC}"
else
    echo -e "${RED}FAIL: reference.dfy does not verify:${NC}"
    echo "$REF_OUTPUT" | head -30
    ERRORS=$((ERRORS + 1))
fi

# 3. tests.dfy should compile AND verify
echo ""
echo "--- Checking tests.dfy (should verify) ---"
TEST_OUTPUT=$("$DOTNET" "$DAFNY_DLL" verify "$PROBLEM_DIR/tests.dfy" 2>&1 || true)
if echo "$TEST_OUTPUT" | grep -q "0 errors"; then
    echo -e "${GREEN}PASS: tests.dfy verifies successfully${NC}"
else
    echo -e "${RED}FAIL: tests.dfy does not verify:${NC}"
    echo "$TEST_OUTPUT" | head -30
    ERRORS=$((ERRORS + 1))
fi

# Summary
echo ""
echo "========================================"
if [ $ERRORS -eq 0 ]; then
    echo -e "${GREEN}RESULT: $PROBLEM_ID -- ALL CHECKS PASSED${NC}"
else
    echo -e "${RED}RESULT: $PROBLEM_ID -- $ERRORS CHECK(S) FAILED${NC}"
fi
echo "========================================"

exit $ERRORS

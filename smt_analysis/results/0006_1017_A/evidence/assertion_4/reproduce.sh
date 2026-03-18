#!/bin/bash
SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
DOTNET="/opt/homebrew/Cellar/dotnet@8/8.0.124/libexec/dotnet"
DAFNY_DLL="/Users/mchiesa/work/projects/2026-02-dafny-liftings/dafny-source/Binaries/Dafny.dll"

echo "=== With assertion (should pass) ==="
"$DOTNET" "$DAFNY_DLL" verify "$SCRIPT_DIR/with_assertion.dfy" --verification-time-limit 60

echo ""
echo "=== Without assertion (should fail) ==="
"$DOTNET" "$DAFNY_DLL" verify "$SCRIPT_DIR/without_assertion.dfy" --verification-time-limit 60

echo ""
echo "=== Ghost vars only (should fail) ==="
"$DOTNET" "$DAFNY_DLL" verify "$SCRIPT_DIR/ghost_var_variant.dfy" --verification-time-limit 60

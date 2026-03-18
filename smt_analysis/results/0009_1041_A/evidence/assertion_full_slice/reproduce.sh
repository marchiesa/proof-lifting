#!/bin/bash
echo "=== With assertion (should pass) ==="
dafny verify with_assertion.dfy --verification-time-limit 60
echo "=== Without assertion (should fail) ==="
dafny verify without_assertion.dfy --verification-time-limit 60
echo "=== Ghost vars only (should fail) ==="
dafny verify ghost_var_variant.dfy --verification-time-limit 60

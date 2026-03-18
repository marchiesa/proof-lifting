#!/bin/bash
echo "=== With MaxPurchasesBound call (should pass) ==="
dafny verify with_assertion.dfy --verification-time-limit 60
echo ""
echo "=== Without MaxPurchasesBound call (should fail) ==="
dafny verify without_assertion.dfy --verification-time-limit 60

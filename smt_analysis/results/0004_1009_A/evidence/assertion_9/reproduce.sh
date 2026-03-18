#!/bin/bash
echo "=== With GreedyBuyOptimal call (should pass) ==="
dafny verify with_assertion.dfy --verification-time-limit 60
echo ""
echo "=== Without GreedyBuyOptimal call (should fail) ==="
dafny verify without_assertion.dfy --verification-time-limit 60

# Problem 4: Minimum Coin Change with Optimality Proof

## Task
Given coin denominations and a target amount, find the minimum number of coins needed using dynamic programming. The spec requires proving both FEASIBILITY (a valid combination exists) and OPTIMALITY (no combination uses fewer coins).

## Why This Is Hard

1. **Optimality requires universal quantification over all combinations**: The spec says `forall combo :: IsValidCombination(...) ==> TotalCoins(combo) >= result`. This is not just about computing the right answer — it's about proving no better answer exists.

2. **DP table correctness is inductive**: The invariant must state that `dp[j]` for all processed amounts is optimal. This requires an inductive argument: when processing coin `coins[i]`, the subproblem `dp[j - coins[i]]` was already optimal using coins `coins[0..i]`.

3. **Three nested reasoning levels**: (a) outer loop over coin types, (b) inner loop over amounts, (c) the optimality argument comparing against ALL possible combinations.

4. **Connecting imperative DP to declarative spec**: The DP recurrence `dp[j] = min(dp[j], dp[j-c]+1)` must be linked to `DotProduct` and `TotalCoins` over arbitrary combination vectors. The prover must understand that the DP explores all feasible ways to use coin `c`.

5. **Handling impossibility**: When `result == -1`, the spec requires proving NO valid combination exists. The invariant must track which amounts are achievable with the coins processed so far.

6. **Array vs. functional reasoning**: The implementation uses a mutable array, but the spec uses pure functions (DotProduct, TotalCoins). Bridging this gap requires frame conditions on the array.

## Expected Invariants
- Init loop: `dp[j] == -1` for `1 <= j < init` and `dp[0] == 0`
- Outer loop: `dp[j]` is optimal using only `coins[0..i]` for all `j`
- Inner loop: `dp[j]` is optimal using `coins[0..i+1]` for `j < current`, and using `coins[0..i]` for `j >= current`

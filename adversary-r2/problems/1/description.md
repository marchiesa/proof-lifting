# Problem 1: 0/1 Knapsack with Optimality Proof

## Description

Implement the classic 0/1 Knapsack problem using dynamic programming. Given a list of items (each with a weight and value) and a capacity, find the maximum total value achievable by selecting a subset of items whose total weight does not exceed the capacity.

## Why This Is Hard

The **optimality spec** requires proving that no subset of items with total weight <= capacity achieves a higher value than the one returned. This demands:

1. A formal definition of "valid subset" (total weight within capacity).
2. A formal definition of "value of a subset."
3. The DP recurrence must be shown correct: `dp[i][w] = max(dp[i-1][w], dp[i-1][w - weights[i]] + values[i])`.
4. An inductive proof that `dp[n][W]` equals the maximum over ALL 2^n subsets — this is the crux.

The prover must establish that the DP table at each cell represents the optimal value considering items 0..i-1 with capacity w. This requires ~100+ lines of careful inductive lemmas, especially the "no better subset exists" direction.

## Specification Strength

- **Feasibility**: The returned value corresponds to some valid subset.
- **Optimality**: No valid subset achieves a strictly higher value.

## Expected Difficulty: VERY HARD

The prover failed on min coin change optimality in round 1. Knapsack optimality is structurally similar but with two dimensions (items and capacity), making the induction more complex.

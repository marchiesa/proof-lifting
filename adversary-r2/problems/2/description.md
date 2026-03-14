# Problem 2: Longest Increasing Subsequence (LIS) with Optimality Proof

## Description

Given a sequence of integers, find the length of the longest strictly increasing subsequence. Use the classic O(n^2) DP approach where `dp[i]` is the length of the longest increasing subsequence ending at index `i`.

## Why This Is Hard

The **optimality spec** requires proving that no strictly increasing subsequence of the input has length greater than the returned value. This requires:

1. A formal definition of "increasing subsequence" as a sequence of indices `i_0 < i_1 < ... < i_k` where `a[i_0] < a[i_1] < ... < a[i_k]`.
2. Proving the DP recurrence is correct: `dp[i] = 1 + max { dp[j] : j < i and a[j] < a[i] }`.
3. An inductive argument that the maximum of `dp[0..n-1]` equals the length of the longest increasing subsequence over ALL possible subsequences.

The subsequence definition is particularly tricky because subsequences are defined by index sequences (not contiguous), requiring quantification over all possible index sequences of arbitrary length.

## Specification Strength

- **Feasibility**: There exists an increasing subsequence of the returned length.
- **Optimality**: No increasing subsequence has greater length.
- **Witness**: The actual subsequence (indices) is returned as a ghost witness.

## Expected Difficulty: VERY HARD

Quantifying over all possible subsequences (exponentially many) and proving none is longer requires deep inductive reasoning about the DP table.

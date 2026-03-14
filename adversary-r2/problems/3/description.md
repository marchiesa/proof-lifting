# Problem 3: Edit Distance (Levenshtein) with Optimality Proof

## Description

Compute the minimum edit distance between two strings. The allowed operations are:
- **Insert** a character
- **Delete** a character
- **Replace** a character

Each operation has cost 1. Use the classic 2D DP approach where `dp[i][j]` is the edit distance between the first `i` characters of string `s` and the first `j` characters of string `t`.

## Why This Is Hard

The **optimality spec** requires proving that no sequence of edit operations transforms `s` into `t` with fewer operations. This demands:

1. A formal definition of "edit operation sequence" (a sequence of inserts, deletes, replaces).
2. A formal definition of "applying a sequence of edit operations to a string yields another string."
3. Proving the DP recurrence correctly captures the minimum.
4. An inductive proof that `dp[|s|][|t|]` is the minimum over ALL possible edit sequences.

The challenge is that the space of edit sequences is infinite (you can insert then delete arbitrarily). The standard proof uses a structural argument about optimal alignments, which is hard to formalize.

## Specification Strength

- **Correctness**: The returned value equals `dp[|s|][|t|]`.
- **Optimality**: No edit sequence transforming `s` to `t` has cost less than the returned value.

## Expected Difficulty: VERY HARD

The edit sequence formalization requires reasoning about string transformations, and the optimality proof requires showing the DP captures all possible transformation paths.

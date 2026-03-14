# Problem 6: Interval Scheduling Maximization with Optimality (Greedy)

## Description

Given a set of intervals [start, end), find the maximum number of non-overlapping intervals using the greedy algorithm: sort by end time, then greedily pick the earliest-ending interval that doesn't overlap with the last selected one.

## Why This Is Hard

The **optimality spec** requires a formal **exchange argument**: prove that no selection of non-overlapping intervals contains more intervals than the greedy solution. This is fundamentally different from DP optimality proofs because:

1. **Exchange argument structure**: Must show that for any optimal solution OPT, you can transform it into the greedy solution without losing intervals. Specifically, the i-th interval in greedy ends no later than the i-th interval in any valid selection.
2. **Sorting precondition**: Must prove the array is correctly sorted by end time, and the sorted order is a permutation.
3. **Non-overlapping definition**: Two intervals [s1, e1) and [s2, e2) don't overlap iff e1 <= s2 or e2 <= s1.
4. **Inductive exchange lemma**: For any alternative selection of non-overlapping intervals with k elements, show the greedy solution has at least k elements.

The exchange argument requires careful induction where at each step you show "greedy's i-th choice is at least as good as any alternative's i-th choice" (ends no later), which requires nested quantifiers over all possible alternative solutions.

## Specification Strength

- **Feasibility**: The returned selection consists of non-overlapping intervals.
- **Optimality**: No selection of non-overlapping intervals has more elements.
- **Subset property**: The returned intervals are a subset of the input intervals.

## Expected Difficulty: VERY HARD

Exchange arguments are a different proof paradigm from DP induction. The prover must reason about arbitrary alternative solutions and show the greedy solution dominates them step-by-step.

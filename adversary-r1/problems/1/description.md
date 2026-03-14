# Problem 1: Matrix Row-wise Prefix Sums

## Task
Given a `seq<seq<int>>` representing a matrix, compute the row-wise prefix sums. Each element `output[i][j]` equals the sum of `input[i][0..j+1]`.

## Why This Is Hard

1. **Nested loops with nested quantifiers**: The outer loop iterates over rows, the inner loop over columns. The spec uses `forall i, j` ranging over both dimensions, so the invariant must quantify over already-processed rows AND the current partial row.

2. **Linking running sum to SumRange**: The inner loop accumulates a running sum, but the spec uses a recursive `SumRange` function. The prover must discover an invariant relating the imperative running-sum accumulator to the declarative recursive definition.

3. **Sequence construction**: Both rows and the matrix are built incrementally via concatenation. The invariant must express that `output[k]` for already-processed rows `k < i` satisfies the spec, while the current row is being built element-by-element.

4. **Two-level preservation**: When a new row is appended to `output`, the prover must show all previously computed rows are unchanged. This requires reasoning about sequence indexing after concatenation.

## Expected Invariants
- Outer loop: `|output| == i`, and for all processed rows, the spec holds
- Inner loop: `|prefixRow| == j`, `runningSum == SumRange(row, 0, j)`, and each element of `prefixRow` is correct

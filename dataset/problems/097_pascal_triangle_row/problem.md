# Pascal's Triangle Row Computation

## Description

Compute the nth row of Pascal's triangle using the recurrence relation
C(n,k) = C(n-1,k-1) + C(n-1,k).

## Input

- `n`: a natural number (the row index, 0-based)

## Output

A sequence `row` of length n+1 where `row[k] == C(n, k)` for all 0 <= k <= n.

## Examples

- `ComputePascalRow(0)` returns `[1]`
- `ComputePascalRow(1)` returns `[1, 1]`
- `ComputePascalRow(4)` returns `[1, 4, 6, 4, 1]`

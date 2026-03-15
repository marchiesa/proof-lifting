# Two Sum (Two Pointer)

## Description

Given a sorted sequence and a target value, determine if there exist two distinct
elements that sum to the target. Uses the two-pointer technique.

## Input

- `a`: a sorted sequence of integers
- `target`: target sum

## Output

- `found`: whether a pair exists
- `lo`, `hi`: indices of the pair (if found)

## Examples

- `TwoSumSorted([1, 2, 3, 4, 5], 5)` returns `(true, 0, 3)` since 1+4=5
- `TwoSumSorted([1, 2, 3], 10)` returns `(false, _, _)`

# Two Sum (Sorted Array)

## Description

Given a sorted sequence of integers and a target sum, determine whether there exist
two distinct indices i and j such that a[i] + a[j] == target. Use the two-pointer
technique: start with pointers at both ends and move them inward.

## Input

- `a`: a sequence of integers sorted in non-decreasing order
- `target`: the desired sum

## Output

A boolean `found` and two indices `i`, `j` such that:
- If `found` is true: `0 <= i < j < |a|` and `a[i] + a[j] == target`
- If `found` is false: no such pair exists in `a`

## Examples

- `TwoSum([1, 2, 3, 4, 6], 8)` returns `(true, 1, 4)` since `2 + 6 == 8`
- `TwoSum([1, 2, 3], 10)` returns `(false, _, _)`
- `TwoSum([], 5)` returns `(false, _, _)`

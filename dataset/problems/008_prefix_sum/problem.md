# Prefix Sum

## Description

Given a sequence of integers, compute the prefix sum array. Element `i` of the
output is the sum of elements `a[0..i]` (inclusive).

## Input

- `a`: a sequence of integers

## Output

A sequence `p` of the same length where `p[i] == a[0] + a[1] + ... + a[i]` for all `i`.

## Examples

- `PrefixSum([1, 2, 3, 4])` returns `[1, 3, 6, 10]`
- `PrefixSum([5])` returns `[5]`
- `PrefixSum([])` returns `[]`
- `PrefixSum([-1, 1, -1, 1])` returns `[-1, 0, -1, 0]`

# Check if Array is a Permutation of 0..n-1

## Description

Given a sequence of integers, determine whether it is a permutation of `[0, 1, ..., n-1]`
where `n` is the length of the sequence. This means every element is in range `[0, n)` and
all elements are distinct.

## Input

- `a`: a sequence of integers

## Output

A boolean `result` that is `true` if and only if `a` is a permutation of `0..n-1`.

## Examples

- `CheckPermutation([2, 0, 1])` returns `true`
- `CheckPermutation([0, 1, 5])` returns `false` (5 out of range)
- `CheckPermutation([0, 1, 1])` returns `false` (duplicate)
- `CheckPermutation([])` returns `true`

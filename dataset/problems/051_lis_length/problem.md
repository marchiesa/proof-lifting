# Longest Increasing Subsequence Length

## Description

Given a non-empty sequence of integers, compute the length of the longest strictly
increasing subsequence using dynamic programming.

## Input

- `a`: a non-empty sequence of integers

## Output

An integer `length` such that:
- `length >= 1` (every element is an increasing subsequence of length 1)
- `length <= |a|` (cannot be longer than the input)

## Examples

- `LISLength([1, 2, 3, 4, 5])` returns `5`
- `LISLength([5, 4, 3, 2, 1])` returns `1`
- `LISLength([3, 1, 4, 1, 5, 9])` returns `4`
- `LISLength([42])` returns `1`

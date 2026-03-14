# Longest Increasing Subsequence Length

## Description

Given a sequence of integers, compute the length of the longest strictly increasing
subsequence using dynamic programming (O(n^2) approach).

## Input

- `a`: a non-empty sequence of integers

## Output

An integer `length` such that:
- `length >= 1` (a single element is always an increasing subsequence)
- There exists a strictly increasing subsequence of `a` with exactly `length` elements
- No strictly increasing subsequence of `a` has more than `length` elements

## Examples

- `LISLength([10, 9, 2, 5, 3, 7, 101, 18])` returns `4` (subsequence: [2, 3, 7, 18])
- `LISLength([1, 2, 3])` returns `3`
- `LISLength([3, 2, 1])` returns `1`
- `LISLength([5])` returns `1`

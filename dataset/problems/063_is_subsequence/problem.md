# Check if String is Subsequence

## Description

Given two sequences `s` and `t`, check whether `s` is a subsequence of `t`. A subsequence is obtained by deleting zero or more elements from `t` without changing the order of the remaining elements.

## Input

- `s`: a sequence of integers (the potential subsequence)
- `t`: a sequence of integers (the main sequence)

## Output

A boolean that is `true` if and only if `s` is a subsequence of `t`.

## Examples

- `IsSubsequence([1, 3], [1, 2, 3, 4])` returns `true`
- `IsSubsequence([1, 4], [1, 2, 3, 4])` returns `true`
- `IsSubsequence([4, 1], [1, 2, 3, 4])` returns `false`
- `IsSubsequence([], [1, 2, 3])` returns `true`
- `IsSubsequence([1], [])` returns `false`

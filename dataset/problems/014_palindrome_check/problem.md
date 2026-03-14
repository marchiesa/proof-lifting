# Palindrome Check

## Description

Given a sequence of integers, determine whether it reads the same forwards
and backwards.

## Input

- `a`: a sequence of integers

## Output

A boolean `result` such that:
- `result == true` if and only if `forall i :: 0 <= i < |a| ==> a[i] == a[|a| - 1 - i]`

## Examples

- `IsPalindrome([1, 2, 3, 2, 1])` returns `true`
- `IsPalindrome([1, 2, 3])` returns `false`
- `IsPalindrome([])` returns `true`
- `IsPalindrome([42])` returns `true`
- `IsPalindrome([1, 1])` returns `true`

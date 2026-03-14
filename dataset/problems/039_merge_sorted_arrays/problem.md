# Merge Two Sorted Arrays Into One Sorted Array

## Description

Given two sorted arrays, merge them into a single sorted array. The result must be a permutation of the concatenation of both input arrays (proved via multiset equality).

## Input

- `a`: a sorted array of integers
- `b`: a sorted array of integers

## Output

An array `c` such that:
- `c` is sorted
- `c.Length == a.Length + b.Length`
- `multiset(c[..]) == multiset(a[..]) + multiset(b[..])`

## Examples

- `MergeArrays([1, 3, 5], [2, 4, 6])` returns array `[1, 2, 3, 4, 5, 6]`
- `MergeArrays([1, 2, 3], [])` returns array `[1, 2, 3]`

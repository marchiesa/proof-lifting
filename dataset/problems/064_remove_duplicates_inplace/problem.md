# Remove Duplicates from Sorted Array (In-Place)

## Description

Given a sorted array of integers, remove duplicates in-place using a two-pointer technique. Return the new length `k` such that the first `k` elements of the array contain the unique elements in sorted order.

## Input

- `a`: an array of integers sorted in non-decreasing order

## Output

An integer `k` such that:
- `a[0..k]` contains only distinct elements
- `a[0..k]` is sorted
- Every element from the original array appears in `a[0..k]`
- `0 <= k <= a.Length`

## Examples

- `RemoveDuplicates([1, 1, 2])` returns `2`, array starts with `[1, 2, ...]`
- `RemoveDuplicates([1, 1, 2, 2, 3])` returns `3`, array starts with `[1, 2, 3, ...]`
- `RemoveDuplicates([1])` returns `1`

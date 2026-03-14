# Kth Smallest Element

## Description

Find the kth smallest element (0-indexed) in a sequence using partial selection sort.

## Input

- `a`: a non-empty sequence of integers
- `k`: a valid index (0 <= k < |a|)

## Output

An integer `result` that is an element of `a` (exists in the multiset).

## Examples

- `KthSmallest([3, 1, 4, 1, 5], 0)` returns `1`
- `KthSmallest([3, 1, 4, 1, 5], 2)` returns `3`
- `KthSmallest([3, 1, 4, 1, 5], 4)` returns `5`

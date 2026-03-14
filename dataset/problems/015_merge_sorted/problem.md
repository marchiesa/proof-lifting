# Merge Two Sorted Sequences

## Description

Given two sorted sequences of integers, merge them into a single sorted sequence
containing all elements from both inputs.

## Input

- `a`: a sequence of integers sorted in non-decreasing order
- `b`: a sequence of integers sorted in non-decreasing order

## Output

A sequence `result` such that:
- `result` is sorted in non-decreasing order
- `result` contains exactly the multiset union of `a` and `b`
- `|result| == |a| + |b|`

## Examples

- `MergeSorted([1, 3, 5], [2, 4, 6])` returns `[1, 2, 3, 4, 5, 6]`
- `MergeSorted([1, 2], [])` returns `[1, 2]`
- `MergeSorted([], [3, 4])` returns `[3, 4]`
- `MergeSorted([1, 1], [1, 1])` returns `[1, 1, 1, 1]`

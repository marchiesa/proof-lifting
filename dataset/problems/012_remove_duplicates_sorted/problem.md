# Remove Duplicates from Sorted Sequence

## Description

Given a sorted sequence of integers, return a new sequence with all duplicate
elements removed. The result should maintain the sorted order and contain each
distinct value exactly once.

## Input

- `a`: a sequence of integers sorted in non-decreasing order

## Output

A sequence `result` such that:
- `result` is sorted in strictly increasing order
- Every element in `result` appears in `a`
- Every element in `a` appears in `result`
- `|result| <= |a|`

## Examples

- `RemoveDuplicates([1, 1, 2, 3, 3, 3, 4])` returns `[1, 2, 3, 4]`
- `RemoveDuplicates([1, 2, 3])` returns `[1, 2, 3]`
- `RemoveDuplicates([])` returns `[]`
- `RemoveDuplicates([5, 5, 5])` returns `[5]`

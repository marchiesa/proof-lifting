# Counting Sort

## Description

Given a sequence of non-negative integers all less than a given bound `maxVal`,
sort the sequence using counting sort. This is a non-comparison-based sorting
algorithm that runs in O(n + maxVal) time.

## Input

- `a`: a sequence of non-negative integers
- `maxVal`: an upper bound such that all elements satisfy `0 <= a[i] < maxVal`

## Output

A sorted sequence `result` that is a permutation of `a`.

## Properties

- The result is sorted in non-decreasing order
- The multiset of elements is preserved
- `|result| == |a|`

## Examples

- `CountingSort([3, 1, 4, 1, 5], 6)` returns `[1, 1, 3, 4, 5]`
- `CountingSort([], 10)` returns `[]`
- `CountingSort([0, 0, 0], 1)` returns `[0, 0, 0]`

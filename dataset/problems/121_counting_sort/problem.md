# Counting Sort

## Description

Sort a sequence of integers that are all in a known range [0, k) using counting sort.
Count the occurrences of each value, then build the sorted output.

## Input

- `a`: a sequence of integers, each in [0, k)
- `k`: a positive integer defining the range

## Output

A sorted sequence that is a permutation of the input.

## Examples

- `CountingSort([2, 0, 1, 2, 0], 3)` returns `[0, 0, 1, 2, 2]`
- `CountingSort([1, 0, 1, 0], 2)` returns `[0, 0, 1, 1]`
- `CountingSort([], 5)` returns `[]`

# Partition Around Pivot

## Description

Given a sequence of integers and a pivot value, partition the sequence into
two parts: elements less than or equal to the pivot, followed by elements
greater than the pivot. Return the partitioned sequence and the split index.

## Input

- `a`: a sequence of integers
- `pivot`: an integer to partition around

## Output

- `result`: a sequence that is a permutation of `a` with elements <= pivot
  before elements > pivot
- `splitIdx`: the index where the partition boundary lies (number of elements <= pivot)

## Examples

- `Partition([3, 1, 4, 1, 5, 9], 3)` returns `([3, 1, 1, ...], 3)` -- first 3 elements are <= 3
- `Partition([1, 2, 3], 0)` returns `([1, 2, 3], 0)` -- all elements > 0
- `Partition([1, 2, 3], 5)` returns `([1, 2, 3], 3)` -- all elements <= 5

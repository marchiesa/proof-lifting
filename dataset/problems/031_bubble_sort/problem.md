# Bubble Sort

## Description

Sort an array of integers in non-decreasing order using the bubble sort algorithm.
The postcondition requires both that the result is sorted and that it is a permutation
of the original array (multiset equality).

## Input

- `a`: an array of integers

## Output

The array `a` is modified in-place such that:
- `a[..]` is sorted in non-decreasing order
- `multiset(a[..])` equals the original multiset

## Examples

- `[3, 1, 4, 1, 5]` becomes `[1, 1, 3, 4, 5]`
- `[5, 4, 3, 2, 1]` becomes `[1, 2, 3, 4, 5]`
- `[]` stays `[]`

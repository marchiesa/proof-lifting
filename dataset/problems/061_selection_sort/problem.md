# Selection Sort

## Description

Sort an array of integers in non-decreasing order using selection sort. In each iteration, find the minimum element in the unsorted portion and swap it into position.

## Input

- `a`: an array of integers

## Output

The array `a` is modified in-place so that:
- The elements are in non-decreasing order
- The resulting array is a permutation of the original (multiset equality)

## Examples

- `SelectionSort([3, 1, 2])` produces `[1, 2, 3]`
- `SelectionSort([5, 3, 1, 4, 2])` produces `[1, 2, 3, 4, 5]`
- `SelectionSort([1])` produces `[1]`
- `SelectionSort([])` produces `[]`

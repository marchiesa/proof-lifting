# Binary Search

## Description

Given a sorted sequence of integers and a target value, find the index of the target
in the sequence. If the target is not present, return -1.

## Input

- `a`: a sequence of integers sorted in non-decreasing order
- `target`: an integer to search for

## Output

An integer `index` such that:
- If `target` exists in `a`: `a[index] == target` and `0 <= index < |a|`
- If `target` does not exist in `a`: `index == -1`

## Examples

- `BinarySearch([1, 3, 5, 7, 9], 5)` returns `2`
- `BinarySearch([1, 3, 5, 7, 9], 4)` returns `-1`
- `BinarySearch([], 1)` returns `-1`
- `BinarySearch([42], 42)` returns `0`

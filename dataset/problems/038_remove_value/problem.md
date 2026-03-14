# Remove All Occurrences of Value from Array

## Description

Given a sequence of integers and a value, return a new sequence with all occurrences of that value removed. The relative order and count of all other elements must be preserved.

## Input

- `a`: a sequence of integers
- `val`: the integer value to remove

## Output

A sequence `result` such that:
- No element in `result` equals `val`
- For every other value `x != val`, the count in `result` equals the count in `a`
- Every element of `result` appears in `a`

## Examples

- `RemoveValue([1, 2, 3, 2, 1], 2)` returns `[1, 3, 1]`
- `RemoveValue([7, 7, 7], 7)` returns `[]`
- `RemoveValue([1, 2, 3], 5)` returns `[1, 2, 3]`

# Move Zeroes to End

## Description

Given a sequence of integers, move all zeroes to the end while maintaining the relative order of non-zero elements.

## Input

- `a`: a sequence of integers

## Output

A sequence `result` where:
- Non-zero elements appear first, in their original order
- All remaining positions are zero
- Length is preserved

## Examples

- `MoveZeroes([0, 1, 0, 3, 12])` returns `[1, 3, 12, 0, 0]`
- `MoveZeroes([0, 0, 0])` returns `[0, 0, 0]`
- `MoveZeroes([1, 2, 3])` returns `[1, 2, 3]`

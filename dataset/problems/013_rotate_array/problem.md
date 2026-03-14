# Rotate Array

## Description

Given a sequence of integers and a non-negative integer `k`, rotate the sequence
to the right by `k` positions. Elements that fall off the end wrap around to the beginning.

## Input

- `a`: a sequence of integers
- `k`: a non-negative integer (rotation amount)

## Output

A sequence `result` such that:
- `|result| == |a|`
- For all valid indices `i`: `result[(i + k) % |a|] == a[i]`
- The multiset of elements is preserved

## Examples

- `Rotate([1, 2, 3, 4, 5], 2)` returns `[4, 5, 1, 2, 3]`
- `Rotate([1, 2, 3], 0)` returns `[1, 2, 3]`
- `Rotate([1, 2, 3], 3)` returns `[1, 2, 3]`
- `Rotate([], 5)` returns `[]`

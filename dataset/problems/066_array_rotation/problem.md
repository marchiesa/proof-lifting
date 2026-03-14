# Array Rotation by K Positions

## Description

Rotate an array of integers to the left by `k` positions. Element at index `i` moves to index `(i - k) mod n`.

## Input

- `a`: an array of integers
- `k`: number of positions to rotate left (0 <= k)

## Output

The array `a` is modified in-place such that the new `a[i]` equals the old `a[(i + k) mod n]`.

## Examples

- `Rotate([1, 2, 3, 4, 5], 2)` produces `[3, 4, 5, 1, 2]`
- `Rotate([1, 2, 3], 0)` produces `[1, 2, 3]`
- `Rotate([1, 2, 3], 3)` produces `[1, 2, 3]`

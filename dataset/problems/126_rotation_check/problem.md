# Rotation Check

## Description

Check if one sequence is a rotation of another. A sequence `b` is a rotation of `a`
if there exists some `k` such that `b == a[k..] + a[..k]`.

## Input

- `a`, `b`: two sequences of integers

## Output

`true` if `b` is a rotation of `a`, `false` otherwise.

## Examples

- `CheckRotation([1,2,3], [2,3,1])` returns `true`
- `CheckRotation([1,2,3], [1,3,2])` returns `false`

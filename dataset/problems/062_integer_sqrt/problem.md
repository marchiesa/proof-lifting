# Integer Square Root (Binary Search on Answer)

## Description

Compute the integer square root of a non-negative integer `n`. That is, find the largest integer `r` such that `r * r <= n`.

## Input

- `n`: a non-negative integer

## Output

An integer `r` such that:
- `r >= 0`
- `r * r <= n`
- `(r + 1) * (r + 1) > n`

## Examples

- `IntSqrt(0)` returns `0`
- `IntSqrt(1)` returns `1`
- `IntSqrt(4)` returns `2`
- `IntSqrt(8)` returns `2`
- `IntSqrt(9)` returns `3`
- `IntSqrt(100)` returns `10`

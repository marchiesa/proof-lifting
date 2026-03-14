# Fast Exponentiation (Exponentiation by Squaring)

## Description

Compute `base^exp` using the fast exponentiation (repeated squaring) algorithm in O(log exp) multiplications.

## Input

- `base`: an integer
- `exp`: a non-negative integer

## Output

An integer `result` equal to `Power(base, exp)`.

## Examples

- `FastPow(2, 10)` returns `1024`
- `FastPow(5, 0)` returns `1`
- `FastPow(7, 1)` returns `7`
- `FastPow(-2, 3)` returns `-8`

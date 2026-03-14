# Flatten Matrix (Row-Major Order)

## Description

Given a matrix (sequence of rows), flatten it into a single sequence in row-major order.

## Input

- `m`: a matrix (sequence of sequences of equal length)
- `rows`: number of rows
- `cols`: number of columns

## Output

A sequence `result` containing all matrix elements in row-major order.

## Examples

- `Flatten([[1,2,3],[4,5,6]], 2, 3)` returns `[1,2,3,4,5,6]`
- `Flatten([[1,2,3]], 1, 3)` returns `[1,2,3]`
- `Flatten([], 0, 0)` returns `[]`

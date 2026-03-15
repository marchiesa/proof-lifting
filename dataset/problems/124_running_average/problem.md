# Running Average (Partial Sums)

## Description

Compute the sequence of partial sums of an input sequence.
The i-th element of the result is the sum of the first i+1 elements of the input.

## Input

- `a`: a sequence of integers

## Output

A sequence `result` where `result[i] == Sum(a[0..i+1])`.

## Examples

- `PartialSums([1, 2, 3])` returns `[1, 3, 6]`
- `PartialSums([3, -1, 4])` returns `[3, 2, 6]`
- `PartialSums([])` returns `[]`

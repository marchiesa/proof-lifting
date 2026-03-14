# Sliding Window Maximum

## Description

Given a sequence of integers and a window size `w`, compute the maximum value
in each window of size `w` as it slides across the sequence.

## Input

- `a`: a non-empty sequence of integers
- `w`: window size, `1 <= w <= |a|`

## Output

A sequence `result` of length `|a| - w + 1` where `result[i]` is the maximum
of `a[i..i+w]`.

## Examples

- `SlidingMax([1,3,-1,-3,5,3,6,7], 3)` returns `[3,3,5,5,6,7]`
- `SlidingMax([1,2,3], 1)` returns `[1,2,3]`
- `SlidingMax([1,2,3], 3)` returns `[3]`

# Reverse Sequence

## Description

Given a sequence of integers, produce the reversed sequence by building it
iteratively. The reversal is done element-by-element using a loop.

## Input

- `a`: a sequence of integers

## Output

A sequence `r` that is the reverse of `a`:
- `|r| == |a|`
- For all valid indices `i`: `r[i] == a[|a| - 1 - i]`

## Examples

- `ReverseSeq([1, 2, 3, 4])` returns `[4, 3, 2, 1]`
- `ReverseSeq([])` returns `[]`
- `ReverseSeq([42])` returns `[42]`

# Dutch National Flag

## Description

Given a sequence of integers where each element is 0, 1, or 2, sort the sequence
in-place using the Dutch National Flag algorithm (three-way partitioning). The result
should have all 0s first, then all 1s, then all 2s.

Since Dafny sequences are immutable, we use an array for this problem and return
a sorted copy.

## Input

- `a`: an array of integers where each element is in {0, 1, 2}

## Output

The array `a` is modified in place so that:
- All elements with value 0 come before elements with value 1
- All elements with value 1 come before elements with value 2
- The array is a permutation of the original

## Examples

- `[2, 0, 1, 2, 0, 1]` becomes `[0, 0, 1, 1, 2, 2]`
- `[0, 0, 0]` stays `[0, 0, 0]`
- `[2, 1, 0]` becomes `[0, 1, 2]`

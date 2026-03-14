# Run-Length Compress

## Description

Given a sequence of integers, compress consecutive duplicate elements into (value, count) pairs. Return two parallel sequences: one of values and one of counts.

## Input

- `s`: a sequence of integers

## Output

Two sequences `vals` and `counts` such that:
- `|vals| == |counts|`
- Adjacent values in `vals` are different
- All counts are positive
- Expanding the pairs gives back the original sequence

## Examples

- `Compress([1, 1, 2, 3, 3, 3])` returns `vals=[1, 2, 3]`, `counts=[2, 1, 3]`
- `Compress([5])` returns `vals=[5]`, `counts=[1]`
- `Compress([])` returns `vals=[]`, `counts=[]`

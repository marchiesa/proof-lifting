# Run-Length Encoding

## Description

Given a sequence of integers, produce a run-length encoding: a sequence of
(value, count) pairs where consecutive equal elements are grouped together.

## Input

- `a`: a sequence of integers

## Output

Two sequences `values` and `counts` such that:
- `|values| == |counts|`
- Each count is positive
- Adjacent values are different (no two consecutive runs have the same value)
- Expanding the encoding reconstructs the original sequence

## Examples

- `RLE([1, 1, 2, 2, 2, 3])` returns values=[1,2,3], counts=[2,3,1]
- `RLE([5])` returns values=[5], counts=[1]
- `RLE([])` returns values=[], counts=[]
- `RLE([1, 2, 1])` returns values=[1,2,1], counts=[1,1,1]

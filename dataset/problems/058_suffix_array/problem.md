# Suffix Array Construction

## Description

Construct a suffix array for a non-empty sequence of integers. A suffix array is
a permutation of indices [0, n) that sorts all suffixes of the input in
lexicographic order. This implementation uses a naive O(n^2 log n) approach
with insertion/selection sort on suffix indices.

## Input

- `s`: a non-empty sequence of integers

## Output

A sequence `sa` such that:
- `|sa| == |s|`
- `sa` is a permutation of `{0, 1, ..., |s|-1}` (all indices valid and distinct)

## Examples

- `SuffixArray([42])` returns `[0]`
- `SuffixArray([1, 2])` returns a permutation of `[0, 1]`
- `SuffixArray([1, 1, 1])` returns a permutation of `[0, 1, 2]`

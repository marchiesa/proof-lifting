# Prefix Minimum Query (Simulated Segment Tree)

## Description

Build a prefix minimum table from a sequence: for each index i, compute
the minimum of all elements from index 0 to i. This simulates the query
functionality of a segment tree for range-minimum queries starting from 0.

Then answer queries: given an index, return the minimum of a[0..index+1].

## Input

- `a`: a non-empty sequence of integers

## Output

- `prefixMin`: sequence where `prefixMin[i] == min(a[0..i+1])`
- Satisfies `prefixMin[0] == a[0]`
- Each entry is a valid minimum of the prefix

## Examples

- `BuildPrefixMin([3, 1, 4, 1, 5])` returns `[3, 1, 1, 1, 1]`
- `BuildPrefixMin([5, 4, 3, 2, 1])` returns `[5, 4, 3, 2, 1]`
- `BuildPrefixMin([1])` returns `[1]`

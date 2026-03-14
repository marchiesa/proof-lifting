# Edit Distance

## Description

Compute the edit distance (Levenshtein distance) between two sequences of integers
using dynamic programming. The edit distance is the minimum number of insertions,
deletions, and substitutions needed to transform one sequence into the other.

## Input

- `s`: a sequence of integers
- `t`: a sequence of integers

## Output

An integer `dist` such that:
- `dist >= 0`
- `dist <= |s| + |t|` (upper bound: delete all of s, insert all of t)

## Examples

- `EditDistance([1, 2, 3], [1, 2, 3])` returns `0`
- `EditDistance([], [1, 2, 3])` returns `3`
- `EditDistance([1, 2, 3], [])` returns `3`
- `EditDistance([1], [2])` returns `1`

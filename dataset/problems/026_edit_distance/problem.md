# Edit Distance

## Description

Given two sequences of integers, compute the edit distance (Levenshtein distance)
between them using dynamic programming. The edit distance is the minimum number
of insertions, deletions, and substitutions needed to transform one sequence
into the other.

## Input

- `a`: first sequence of integers
- `b`: second sequence of integers

## Output

An integer `dist` representing the edit distance:
- `dist >= 0`
- `dist <= max(|a|, |b|)` (at most we replace everything)
- `dist == 0` if and only if `a == b`

## Examples

- `EditDistance([1,2,3], [1,3])` returns `1` (delete 2)
- `EditDistance([1,2,3], [1,2,3])` returns `0`
- `EditDistance([], [1,2])` returns `2`
- `EditDistance([1], [2])` returns `1` (substitute)

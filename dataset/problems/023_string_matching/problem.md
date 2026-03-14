# String Matching (Naive)

## Description

Given a text and a pattern (both as sequences of integers), find the first
occurrence of the pattern in the text. Return the starting index, or -1 if
the pattern does not appear.

## Input

- `text`: a sequence of integers
- `pattern`: a non-empty sequence of integers

## Output

An integer `index` such that:
- If pattern found: `0 <= index <= |text| - |pattern|` and
  `text[index..index + |pattern|] == pattern`
- If not found: `index == -1` and no position in text matches the pattern

## Examples

- `Match([1,2,3,4,5], [3,4])` returns `2`
- `Match([1,2,3], [4,5])` returns `-1`
- `Match([1,2,1,2,3], [1,2,3])` returns `2`
- `Match([1], [1])` returns `0`

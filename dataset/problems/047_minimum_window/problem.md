# Minimum Window Containing Target Elements

## Description

Given a sequence, a target value, and a count `need`, find the length of the shortest contiguous subarray containing at least `need` occurrences of the target value. Uses the sliding window technique.

## Input

- `a`: a non-empty sequence of integers
- `target`: the target integer value
- `need`: the required number of occurrences (positive)

## Output

An integer `minLen`:
- `-1` if no such window exists
- Otherwise the minimum window length (positive, at most `|a|`)

## Examples

- `MinWindowLength([1, 2, 1, 2, 1], 1, 2)` returns `3`
- `MinWindowLength([1, 2, 3], 1, 2)` returns `-1`

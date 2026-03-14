# Find Peak Element

## Description

Given an array of distinct integers, find a peak element. An element is a peak if it is greater than its neighbors. For boundary elements, only one neighbor needs to be smaller.

The array has distinct elements, so a peak always exists.

## Input

- `a`: an array of distinct integers with length >= 1

## Output

An index `p` such that `a[p]` is a peak element.

## Examples

- `FindPeak([1, 3, 2])` returns `1`
- `FindPeak([5, 1, 2])` returns `0`
- `FindPeak([1, 2, 5])` returns `2`
- `FindPeak([42])` returns `0`

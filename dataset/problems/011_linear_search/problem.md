# Linear Search

## Description

Given a sequence of integers and a predicate (represented by searching for the first
element greater than a given threshold), find the index of the first element satisfying
the condition. If no such element exists, return -1.

## Input

- `a`: a sequence of integers
- `threshold`: an integer

## Output

An integer `index` such that:
- If some element `> threshold` exists: `a[index] > threshold`, `0 <= index < |a|`,
  and no earlier element satisfies the predicate (`forall j :: 0 <= j < index ==> a[j] <= threshold`)
- If no such element exists: `index == -1`

## Examples

- `LinearSearch([1, 3, 5, 7], 4)` returns `2` (first element > 4 is 5 at index 2)
- `LinearSearch([1, 2, 3], 10)` returns `-1`
- `LinearSearch([], 0)` returns `-1`
- `LinearSearch([5, 1, 2], 0)` returns `0`

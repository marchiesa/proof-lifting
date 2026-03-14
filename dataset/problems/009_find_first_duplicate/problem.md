# Find First Duplicate

## Description

Given a sequence of integers, find the index of the first element that has
appeared previously in the sequence. If all elements are distinct, return -1.

## Input

- `a`: a sequence of integers

## Output

An integer `index` such that:
- If `index >= 0`: `a[index]` appears at some earlier position `j < index`, and
  no element before position `index` is a duplicate
- If `index == -1`: all elements in `a` are distinct

## Examples

- `FindFirstDuplicate([1, 2, 3, 2, 5])` returns `3` (since `a[3]==2` appeared at index `1`)
- `FindFirstDuplicate([1, 2, 3, 4])` returns `-1`
- `FindFirstDuplicate([5, 5])` returns `1`
- `FindFirstDuplicate([])` returns `-1`

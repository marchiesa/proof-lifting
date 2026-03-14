# Is Sorted Check

## Description

Given a sequence of integers, determine whether it is sorted in non-decreasing
order. Return true if sorted, false otherwise. If false, also return a witness
index where the sorting property is violated.

## Input

- `a`: a sequence of integers

## Output

- `sorted`: true if a is sorted in non-decreasing order
- `witness`: if not sorted, an index where `a[witness] > a[witness + 1]`

## Examples

- `IsSortedCheck([1, 2, 3, 4])` returns `(true, _)`
- `IsSortedCheck([1, 3, 2, 4])` returns `(false, 1)` since `a[1]=3 > a[2]=2`
- `IsSortedCheck([])` returns `(true, _)`
- `IsSortedCheck([5])` returns `(true, _)`

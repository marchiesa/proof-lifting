# Kth Largest Element

## Description

Given a sequence of integers and a value k, find the kth largest element in the sequence.
The kth largest element is the element that would be at position k-1 if the sequence were sorted in descending order.

## Input

- `a`: a non-empty sequence of integers
- `k`: an integer with 1 <= k <= |a|

## Output

An integer that is the kth largest element: exactly k-1 elements in the sequence are strictly greater than it (counting with multiplicity), and it appears in the sequence.

## Examples

- `KthLargest([3,2,1,5,6,4], 2)` returns `5`
- `KthLargest([3,2,3,1,2,4,5,5,6], 4)` returns `4`
- `KthLargest([1], 1)` returns `1`

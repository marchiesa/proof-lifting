# Kth Smallest Element

## Description

Given a sequence of integers and a positive integer k (1-indexed), find the kth
smallest element. This is done via a simple selection approach: repeatedly find
and remove the minimum.

## Input

- `a`: a non-empty sequence of integers
- `k`: an integer with `1 <= k <= |a|`

## Output

An integer `result` such that:
- `result` appears in `a`
- There are at least `k` elements in `a` that are `>= result`
- There are at least `k` elements in `a` that are `<= result` (counting multiplicities appropriately)

## Examples

- `KthSmallest([3, 1, 4, 1, 5], 2)` returns `1`
- `KthSmallest([3, 1, 4, 1, 5], 3)` returns `3`
- `KthSmallest([7], 1)` returns `7`

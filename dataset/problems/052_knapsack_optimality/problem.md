# 0/1 Knapsack with Value Bound

## Description

Solve the 0/1 knapsack problem using dynamic programming with a 1D DP array.
Given items with weights and values, and a capacity constraint, find the maximum
total value achievable. The postcondition requires proving the result is non-negative.

## Input

- `weights`: a sequence of positive integers (item weights)
- `values`: a sequence of non-negative integers (item values)
- `capacity`: a non-negative integer (knapsack capacity)

## Output

An integer `maxVal` such that:
- `maxVal >= 0`

## Examples

- `Knapsack01([2, 3, 4], [3, 4, 5], 5)` returns `7` (items 0 and 1)
- `Knapsack01([], [], 10)` returns `0`
- `Knapsack01([5], [10], 5)` returns `10`

# 0/1 Knapsack

## Description

Given n items with weights and values, and a knapsack capacity W, find the
maximum total value of items that can be put in the knapsack without exceeding
the weight capacity. Each item can be used at most once.

Uses the classic DP approach with a 2D table.

## Input

- `weights`: sequence of positive integer weights
- `values`: sequence of positive integer values
- `W`: knapsack capacity (non-negative integer)
- `|weights| == |values|`

## Output

An integer `maxVal` representing the maximum achievable value:
- `maxVal >= 0`
- `maxVal` does not exceed the sum of all values

## Examples

- `Knapsack([1,2,3], [6,10,12], 5)` returns `22` (items 1 and 2)
- `Knapsack([2,3,4,5], [3,4,5,6], 5)` returns `7` (items 0 and 1)
- `Knapsack([1], [10], 0)` returns `0`

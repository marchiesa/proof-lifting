# Stock Buy/Sell (Maximum Profit, One Transaction)

## Description

Given a sequence of stock prices, find the maximum profit achievable with at most one transaction (buy then sell). The postcondition proves the profit is at least as large as any buy-sell pair.

## Input

- `prices`: a non-empty sequence of integers

## Output

An integer `profit` that is:
- Non-negative
- At least `prices[j] - prices[i]` for any valid buy day `i` and sell day `j > i`

## Examples

- `BestProfit([7, 1, 5, 3, 6, 4])` returns `5`
- `BestProfit([7, 6, 4, 3, 1])` returns `0`

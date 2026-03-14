# Coin Change (Minimum Coins, DP)

## Description

Given a set of coin denominations and a target amount, find the minimum number of coins needed to make the amount. Uses dynamic programming. Returns -1 if impossible.

## Input

- `coins`: a non-empty sequence of positive coin values
- `amount`: a non-negative target amount

## Output

An integer `result`:
- `-1` if the amount cannot be made with the given coins
- Otherwise the minimum number of coins (non-negative)

## Examples

- `CoinChange([1, 5, 10, 25], 30)` returns `2` (25 + 5)
- `CoinChange([3], 7)` returns `-1`
- `CoinChange([1, 2, 5], 0)` returns `0`

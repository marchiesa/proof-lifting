# Check Balanced Parentheses (Single Type)

## Description

Given a sequence of integers where 0 represents '(' and 1 represents ')',
determine whether the parentheses are balanced. A sequence is balanced if
every prefix has at least as many opening as closing parens, and the total
count of opening equals closing.

## Input

- `s`: a sequence of 0s and 1s

## Output

A boolean `result` that is `true` iff the parenthesization is balanced.

## Examples

- `CheckBalanced([0, 0, 1, 1])` returns `true` (corresponds to "(())")
- `CheckBalanced([1, 0])` returns `false` (corresponds to ")(")
- `CheckBalanced([])` returns `true`

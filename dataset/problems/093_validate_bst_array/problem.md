# Validate BST Property on Array

## Description

Given a sequence of integers, determine if it is strictly sorted (each element
is strictly less than the next). This models validating a BST's in-order traversal.

## Input

- `a`: a sequence of integers

## Output

A boolean `valid` that is true if and only if the sequence is strictly increasing.

## Examples

- `ValidateBST([1, 2, 3, 4, 5])` returns `true`
- `ValidateBST([1, 3, 2, 4, 5])` returns `false`
- `ValidateBST([])` returns `true`
- `ValidateBST([42])` returns `true`

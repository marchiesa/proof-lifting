# Check if Two Strings are Anagrams

## Description

Given two sequences of integers, determine if they are anagrams of each other, i.e., if they contain exactly the same elements with the same multiplicities.

## Input

- `a`: a sequence of integers
- `b`: a sequence of integers

## Output

A boolean that is `true` if and only if `a` and `b` are anagrams (multiset equal).

## Examples

- `AreAnagrams([1, 2, 3], [3, 2, 1])` returns `true`
- `AreAnagrams([1, 2, 2], [2, 1, 2])` returns `true`
- `AreAnagrams([1, 2], [1, 3])` returns `false`
- `AreAnagrams([1, 2], [1, 2, 3])` returns `false`

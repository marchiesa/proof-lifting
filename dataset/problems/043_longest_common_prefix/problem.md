# Longest Common Prefix

## Description

Given an array of strings (represented as `seq<seq<int>>`), find the length of their
longest common prefix.

## Input

- `strs`: a non-empty sequence of non-empty integer sequences

## Output

A natural number `len` such that `strs[0][..len]` is the longest common prefix of all strings.

## Examples

- `LongestCommonPrefix([[1,2,3], [1,2,4], [1,2,5]])` returns `2`
- `LongestCommonPrefix([[1,2,3], [1,2,3]])` returns `3`
- `LongestCommonPrefix([[1,2], [3,4]])` returns `0`

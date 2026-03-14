# Longest Palindromic Substring (Expand Around Center)

## Description

Find the longest palindromic substring in a sequence of integers using the expand-around-center technique. Returns the starting index and length of the longest palindrome found.

## Input

- `s`: a non-empty sequence of integers

## Output

Two integers `start` and `length` such that:
- `s[start..start+length]` is a palindrome
- `length > 0`

## Examples

- `LongestPalindrome([1, 2, 3, 2, 1])` returns `(0, 5)` (the whole sequence)
- `LongestPalindrome([1, 2, 3, 4])` returns some palindrome of length 1

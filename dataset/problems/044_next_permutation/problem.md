# Next Permutation (Lexicographic)

## Description

Rearrange the array into the next lexicographically greater permutation. If the array is already the last permutation (descending order), wrap around to the first permutation (ascending order) and return false.

## Input

- `a`: an array of integers

## Output

- The array is modified in-place to the next permutation
- Returns `true` if a next permutation exists, `false` if wrapped around
- The multiset of elements is preserved

## Examples

- `[1, 2, 3]` becomes `[1, 3, 2]`, returns `true`
- `[3, 2, 1]` becomes `[1, 2, 3]`, returns `false`

# Find Second Maximum

## Description

Find the maximum and second maximum values in a sequence of at least two integers.
The second maximum is the largest value among elements not equal to the maximum
(or equal to the maximum if all elements are the same).

## Input

- `a`: a sequence of at least 2 integers

## Output

Two integers `first` and `second` such that:
- `first` is the maximum of `a`
- `second` is the second largest, and every non-maximum element is at most `second`
- Both values exist in `a`

## Examples

- `SecondMax([3, 1, 4, 1, 5, 9, 2, 6])` returns `(9, 6)`
- `SecondMax([10, 20])` returns `(20, 10)`
- `SecondMax([5, 5, 5])` returns `(5, 5)`

# Maximum Subarray Sum (Kadane's Algorithm)

## Description

Given a non-empty sequence of integers, find the maximum sum of any contiguous
subarray. Use Kadane's algorithm which maintains a running maximum ending at
each position.

## Input

- `a`: a non-empty sequence of integers

## Output

An integer `maxSum` which is the maximum sum over all contiguous subarrays of `a`.

## Examples

- `MaxSubarraySum([-2, 1, -3, 4, -1, 2, 1, -5, 4])` returns `6` (subarray `[4, -1, 2, 1]`)
- `MaxSubarraySum([1])` returns `1`
- `MaxSubarraySum([-1, -2, -3])` returns `-1`
- `MaxSubarraySum([5, 4, -1, 7, 8])` returns `23`

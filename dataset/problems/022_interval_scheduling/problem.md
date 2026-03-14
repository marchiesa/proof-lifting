# Interval Scheduling (Greedy)

## Description

Given a set of intervals sorted by end time, find the maximum number of
non-overlapping intervals using a greedy approach. Two intervals overlap
if one starts before the other ends.

## Input

- `starts`: sequence of interval start times
- `ends`: sequence of interval end times, sorted in non-decreasing order
- All intervals satisfy `starts[i] < ends[i]`

## Output

An integer `count` representing the maximum number of non-overlapping intervals:
- `0 <= count <= |starts|`
- Each selected interval is non-overlapping with all others

## Examples

- `starts=[1,3,0,5,8,5]`, `ends=[2,4,6,7,9,9]` -> `count=4` (intervals [1,2],[3,4],[5,7],[8,9])
- `starts=[1,2,3]`, `ends=[10,11,12]` -> `count=1`

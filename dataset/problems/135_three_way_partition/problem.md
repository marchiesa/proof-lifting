# Three-Way Partition

## Description

Partition an array around a pivot value into three groups:
elements less than, equal to, and greater than the pivot.

## Input

- `a`: an array of integers
- `pivot`: the pivot value

## Output

The array rearranged so all elements < pivot come first, then == pivot, then > pivot.
The multiset of elements is preserved.

## Examples

- `ThreeWayPartition([3,1,2,4,0], 2)` produces `[0,1,2,3,4]` or similar valid partition

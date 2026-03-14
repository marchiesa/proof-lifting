# Convex Hull (Upper Hull via Graham Scan)

## Description

Compute the upper hull of a set of 2D points sorted by x-coordinate using a
simplified Graham scan. The algorithm maintains a stack of point indices and
removes points that create non-right turns.

## Input

- `xs`: x-coordinates of points, sorted in non-decreasing order
- `ys`: y-coordinates of points (same length as `xs`)

## Output

A sequence `hull` of point indices such that:
- `|hull| >= 2`
- All indices are valid: `0 <= hull[i] < |xs|`

## Examples

- Two points: hull contains at least 2 indices
- Collinear points: hull contains at least 2 indices
- Square corners: hull contains valid point indices

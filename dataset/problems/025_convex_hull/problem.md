# Convex Hull (Upper Hull)

## Description

Given a set of 2D points sorted by x-coordinate, compute the upper convex hull
using the monotone chain algorithm. The upper hull consists of points such that
all other points lie below the line segments connecting consecutive hull points.

We use the cross product to determine turns: for three points p1, p2, p3,
if `cross(p1, p2, p3) >= 0`, the turn is non-left (right or collinear), and
p2 should be removed from the hull.

## Input

- `xs`: x-coordinates, sorted in non-decreasing order
- `ys`: y-coordinates
- `|xs| == |ys| >= 1`

## Output

- `hull`: sequence of indices into the input that form the upper hull
- Hull points are a subsequence of the input (indices in increasing order)
- Hull has at least 1 point

## Examples

- Points: (0,0), (1,2), (2,1), (3,0) -> upper hull includes (0,0), (1,2), (3,0)

# Shortest Path in Grid

## Description

Find the shortest path length from top-left to bottom-right in a 2D grid.
Cells are 0 (passable) or 1 (blocked). Move in 4 directions.

## Input

- `grid`: a rectangular grid of 0s and 1s
- `rows`, `cols`: dimensions

## Output

The shortest distance, or -1 if no path exists.

## Examples

- `ShortestPath([[0,0],[0,0]], 2, 2)` returns `2`
- `ShortestPath([[0,1],[1,0]], 2, 2)` returns `-1`

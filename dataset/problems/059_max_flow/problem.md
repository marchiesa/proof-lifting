# Max Flow (Bounded Ford-Fulkerson)

## Description

Compute the maximum flow from a source to a sink in a directed graph with
non-negative capacities, using a bounded version of the Ford-Fulkerson algorithm
with BFS augmenting paths (Edmonds-Karp style). The capacity matrix is modified
to represent residual capacities.

## Input

- `n`: number of vertices (positive integer)
- `cap`: an n x n capacity matrix with non-negative values
- `source`: source vertex (valid index, different from sink)
- `sink`: sink vertex (valid index, different from source)

## Output

An integer `flow` such that:
- `flow >= 0`

## Examples

- Direct edge `0 -> 1` with capacity 10: flow >= 0
- No edges (all zero capacity): flow >= 0
- Path `0 -> 1 -> 2` with capacities 5, 3: flow >= 0

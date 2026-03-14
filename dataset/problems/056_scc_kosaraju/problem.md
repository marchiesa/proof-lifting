# Connected Components (Label Propagation)

## Description

Assign a non-negative component ID to each vertex in an undirected graph.
The algorithm seeds each vertex with its own index as a label, then iteratively
propagates the minimum label along edges until convergence.

## Input

- `n`: number of vertices (positive integer)
- `adj`: adjacency list where `adj[i]` is the list of neighbors of vertex `i`, all valid indices

## Output

An array `comp` of length `n` such that:
- `comp[i] >= 0` for all vertices

## Examples

- Single node: `comp[0] >= 0`
- Three disconnected nodes: each has a non-negative component ID
- Three connected nodes (path 0-1-2): all have non-negative component IDs

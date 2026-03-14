# Floyd-Warshall All-Pairs Shortest Paths

## Description

Compute all-pairs shortest paths using the Floyd-Warshall algorithm on a graph
with non-negative edge weights. The graph is represented as an edge list of
(source, destination, weight) triples. Unreachable pairs have distance Inf().

## Input

- `n`: number of vertices (positive integer)
- `edges`: sequence of (source, destination, weight) triples with valid vertex indices and non-negative weights

## Output

A 2D array `dist` of size n x n such that:
- `dist[i, i] == 0` for all vertices (self-distance is zero)
- `dist[i, j] <= Inf()` for all pairs (bounded distances)

## Examples

- Single node, no edges: `dist[0, 0] == 0`
- Three nodes, no edges: diagonal is 0, all others at most Inf()
- Edge `0 -> 1` with weight 3: `dist[0, 0] == 0`, `dist[0, 1] <= Inf()`

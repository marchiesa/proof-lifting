# Bellman-Ford Shortest Paths

## Description

Compute single-source shortest paths using the Bellman-Ford algorithm on a graph
with non-negative edge weights. The graph is represented as an edge list of
(source, destination, weight) triples. Unreachable vertices have distance Inf().

## Input

- `n`: number of vertices (positive integer)
- `edges`: sequence of (source, destination, weight) triples with valid vertex indices and non-negative weights
- `source`: the source vertex (valid index)

## Output

An array `dist` of length `n` such that:
- `dist[source] == 0`
- `forall v :: 0 <= v < n ==> dist[v] <= Inf()`

## Examples

- Single node, no edges: `dist[0] == 0`
- Three nodes, no edges: `dist[0] == 0`, others at most Inf()
- Simple path `0 -> 1` with weight 5: `dist[0] == 0`, `dist[1] <= Inf()`

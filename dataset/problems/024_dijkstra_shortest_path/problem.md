# Dijkstra's Shortest Path (Simplified)

## Description

Given a weighted directed graph as an adjacency matrix with non-negative weights
(where -1 means no edge), and a source node, compute the shortest distance from
the source to all other nodes using Dijkstra's algorithm.

## Input

- `graph`: n x n adjacency matrix of non-negative weights (-1 = no edge)
- `src`: source node, `0 <= src < n`

## Output

- `dist`: sequence of distances, where `dist[i]` is the shortest distance from
  `src` to node `i`. `dist[src] == 0`. If unreachable, `dist[i] == -1`.

## Key Property

For every edge (u, v) with weight w, the triangle inequality holds:
`dist[v] <= dist[u] + w` (when both are reachable).

## Examples

- Graph `[[0,4,-1],[−1,0,1],[−1,−1,0]]`, src=0: dist=[0,4,5]

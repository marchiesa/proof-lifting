# Dijkstra Single Source Shortest Path (Array-Based)

## Description

Given a weighted directed graph represented as an adjacency matrix, compute the shortest distances from a source vertex to all other vertices using Dijkstra's algorithm. Edge weights are non-negative. Use -1 to represent infinity (unreachable).

## Input

- `graph`: adjacency matrix where `graph[i][j]` is the weight of edge i->j, or -1 if no edge
- `n`: number of vertices
- `src`: source vertex

## Output

A sequence `dist` of length `n` where `dist[i]` is the shortest distance from `src` to `i`, or -1 if unreachable.

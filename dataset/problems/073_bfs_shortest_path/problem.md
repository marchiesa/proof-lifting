# BFS Shortest Path in Unweighted Graph

## Description

Given an unweighted directed graph as an adjacency matrix and a source vertex, compute the shortest distances from the source to all vertices using BFS.

## Input

- `graph`: boolean adjacency matrix
- `n`: number of vertices
- `src`: source vertex

## Output

A sequence `dist` of length `n` where `dist[i]` is the shortest distance from `src` to `i`, or -1 if unreachable.

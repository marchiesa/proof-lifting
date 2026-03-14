# Topological Sort Existence (Cycle Detection)

## Description

Given a directed graph represented as an adjacency matrix (where `graph[i][j] == 1`
means there is an edge from node i to node j), determine whether the graph contains
a cycle. This is done by attempting to compute a topological ordering using Kahn's
algorithm (BFS-based). If all nodes are processed, no cycle exists.

## Input

- `graph`: an n x n adjacency matrix (`seq<seq<int>>`) with 0/1 entries
- `n`: number of nodes

## Output

- `acyclic`: boolean, true if the graph has no cycle
- `order`: if acyclic, a valid topological ordering (permutation of 0..n-1)

## Examples

- DAG `{0->1, 0->2, 1->2}`: acyclic = true, order = [0, 1, 2]
- Cycle `{0->1, 1->0}`: acyclic = false

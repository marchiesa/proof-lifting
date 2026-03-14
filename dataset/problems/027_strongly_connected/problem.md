# Strongly Connected Components (Reachability Matrix)

## Description

Given a directed graph as an adjacency matrix, compute the transitive closure
(reachability matrix) using the Floyd-Warshall approach. Two nodes are in the
same strongly connected component if and only if they can reach each other.

Then count the number of strongly connected components.

## Input

- `graph`: n x n boolean adjacency matrix
- `n`: number of nodes

## Output

- `reach`: n x n boolean reachability matrix where `reach[i][j]` is true iff
  there is a path from i to j
- `numSCC`: number of strongly connected components

## Properties

- `reach[i][i]` is true for all i (reflexivity)
- If `reach[i][j]` and `reach[j][k]` then `reach[i][k]` (transitivity)

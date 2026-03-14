# Problem 5: Topological Sort with Completeness and Cycle Detection

## Description

Given a directed graph, either produce a topological ordering or detect that a cycle exists. A topological ordering is a sequence containing all nodes such that for every edge (u, v), u appears before v in the sequence.

## Why This Is Hard

The spec requires THREE properties:

1. **Permutation**: The output is a permutation of all nodes.
2. **Ordering**: For every edge (u, v), u appears before v.
3. **Cycle detection completeness**: If the algorithm reports "has cycle", then there truly EXISTS a cycle in the graph. Conversely, if it returns an ordering, no cycle exists.

The cycle detection proof is the hardest part:
- Must formally define "cycle" (a path from v back to v of length >= 1).
- Must prove the DFS-based algorithm correctly identifies back edges.
- Must show that a back edge implies a cycle EXISTS (constructive proof).
- Must prove that if DFS completes without finding a back edge, NO cycle exists (requires arguing about DFS tree properties).

This requires reasoning about DFS states (white/gray/black), back edges, and the relationship between DFS finishing times and topological order.

## Specification Strength

- **Soundness (ordering)**: If ordering returned, it's a valid topological order.
- **Soundness (cycle)**: If cycle detected, a cycle truly exists.
- **Completeness**: The algorithm never incorrectly reports "cycle" for a DAG, and never produces an "ordering" for a graph with cycles.

## Expected Difficulty: VERY HARD

Proving DFS correctly detects all cycles and only cycles requires sophisticated invariants about the DFS state space.

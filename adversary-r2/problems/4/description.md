# Problem 4: Dijkstra's Shortest Path with Optimality Proof

## Description

Given a weighted directed graph with non-negative edge weights and a source node, compute the shortest distance from the source to every other node. Use Dijkstra's algorithm with a simple array-based priority queue (scan for minimum).

## Why This Is Hard

This combines graph reasoning with DP-style optimality. The spec requires:

1. **Reachability reasoning**: Define "path" in a graph, "path weight", "reachable node."
2. **Optimality**: For each node, the computed distance is the minimum weight over ALL paths from source to that node.
3. **Unreachable nodes**: Nodes not reachable from source must be marked with a sentinel (infinity).

Proving Dijkstra's optimality requires the classic "greedy stays ahead" argument:
- When a node is finalized, its distance is optimal.
- This requires showing that any path through unfinalized nodes cannot be shorter.
- The key invariant involves the set of finalized nodes and the triangle inequality.

This is a combination of graph induction + greedy optimality proof, which is significantly harder than pure DP problems.

## Specification Strength

- **Path validity**: Every path used in the spec must be a valid walk in the graph.
- **Optimality**: For each reachable node `v`, `dist[v]` equals the minimum weight path from source to `v`.
- **Unreachability**: For each unreachable node `v`, `dist[v]` is the sentinel value.

## Expected Difficulty: EXTREMELY HARD

BFS reachability alone took 10 attempts. Shortest path OPTIMALITY over weighted graphs adds a whole extra layer.

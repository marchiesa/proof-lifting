# Problem 3: BFS Reachability on Adjacency List Graph

## Task
Given a directed graph as an adjacency list (`seq<seq<int>>`) and a source node, compute the set of all nodes reachable from the source via BFS. The postcondition states the result is exactly the set of reachable nodes (soundness AND completeness).

## Why This Is Hard

1. **Transitive closure reasoning**: Reachability is defined via existentially quantified paths. The invariant must show that every visited node has a path from the source (soundness) AND that no reachable node is missed (completeness).

2. **Ghost path witnesses**: To prove soundness, each visited node needs a witness path. When a neighbor is discovered, the prover must construct a new path by extending an existing one. This requires ghost state (a map from nodes to paths).

3. **Completeness is extremely hard**: Proving that BFS finds ALL reachable nodes requires an argument like "any reachable node not yet visited must have a path that passes through the frontier (queue)." This is essentially the BFS correctness theorem from algorithms textbooks.

4. **Termination**: The prover must find a decreases clause. The natural measure is `|graph| * |graph| - |visited|` (since visited only grows and is bounded), but this requires knowing visited is a subset of valid nodes.

5. **Nested loops**: The inner loop over neighbors must maintain that `visited` only contains valid, reachable nodes, and that the queue frontier property is preserved.

6. **Queue invariant**: The queue must contain only visited nodes, and every visited node must either have been fully explored or be in the queue. This "frontier" property is crucial for completeness.

## Expected Invariants
- Outer: `visited` = set of nodes discovered so far, all reachable. Queue contains unprocessed nodes. Every reachable node not in visited has a path through a queue node.
- Inner: neighbor exploration preserves the above, extending paths for newly discovered nodes.
- Ghost: `paths: map<int, seq<int>>` mapping each visited node to a valid path from source.

# Problem 6: Merkle Tree Construction and Proof Verification

## Task
Build a Merkle tree from a sequence of leaf values and extract/verify a Merkle proof (authentication path) for a given leaf. The spec requires the tree to be correctly constructed layer-by-layer, and the Merkle proof to recompute to the tree root. Three methods: `BuildMerkleTree`, `ComputeLayerImpl`, `ExtractProof`.

## Why This Is Hard

1. **Three interdependent methods**: `BuildMerkleTree` calls `ComputeLayerImpl` which must match the spec function `ComputeNextLayer`. `ExtractProof` must produce a proof that verifies against the tree structure. Each method has its own loops and invariants.

2. **Recursive function vs. iterative implementation**: `ComputeNextLayer` is recursively defined (pairing elements, handling odd lengths), but `ComputeLayerImpl` computes it iteratively. The invariant must track partial computation of the recursive function.

3. **Odd-length layer handling**: When a layer has an odd number of nodes, the last node is paired with 0. This creates a case split in the recursive definition (`ComputeNextLayer` vs `ComputeNextLayerOdd`) that the iterative code must handle correctly.

4. **Proof extraction requires tree structure reasoning**: `ExtractProof` must navigate the tree level by level, identifying sibling nodes. The invariant must track that the partial proof recomputes to the correct intermediate node.

5. **Modular arithmetic**: The hash functions use modular arithmetic, making concrete reasoning about hash values non-trivial. The prover cannot simplify `(a * 31 + b * 37 + 7) % 1000000007` symbolically.

6. **Nested quantifiers in tree validity**: `ValidMerkleTree` quantifies over all layers, each of which involves a function call `ComputeLayer`. The prover must reason about sequence indexing, layer sizes halving, and termination.

7. **Termination of tree construction**: The `while |currentLayer| >= 2` loop must terminate because each layer is strictly shorter. But proving `|ComputeLayer(layer)| < |layer|` requires understanding the recursive structure.

## Expected Invariants
- BuildMerkleTree leaf loop: `|leafLayer| == i` and each element is `HashLeaf(leaves[j])`
- BuildMerkleTree layer loop: `tree` satisfies partial validity, `currentLayer == tree[|tree|-1]`, sizes strictly decrease
- ComputeLayerImpl: `result` equals partial application of `ComputeNextLayer` to `layer[..i]`
- ExtractProof: partial proof recomputes current intermediate hash, `idx` tracks position in current layer

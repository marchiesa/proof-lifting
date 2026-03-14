/*
 * Problem 6: Merkle Tree Construction and Proof Verification
 *
 * Build a Merkle tree from a sequence of leaf values using a hash function,
 * then verify that a given leaf is in the tree by checking a Merkle proof
 * (a sequence of sibling hashes along the path from leaf to root).
 *
 * The hash function is modeled as a pure function with collision-resistance
 * assumed (not proven — we just use a concrete mixing function).
 */

// A simple hash combiner: combines two values into one
// Using a polynomial-style mixing function
function HashCombine(left: int, right: int): int
{
  // Mix with a prime multiplier and XOR-like operation
  // We use modular arithmetic to keep values bounded
  ((left * 31 + right * 37 + 7) % 1000000007)
}

// Hash a single leaf
function HashLeaf(v: int): int
{
  ((v * 53 + 13) % 1000000007)
}

// Build the Merkle tree layer by layer.
// A Merkle tree for n leaves has ceil(log2(n)) layers.
// Each layer halves the number of nodes (padding with 0 if odd).
// The tree is represented as seq<seq<int>> where tree[0] is the leaf layer
// and tree[|tree|-1] is the root layer (length 1).

// Compute one layer from the layer below
function ComputeNextLayer(layer: seq<int>): seq<int>
  requires |layer| >= 2
  decreases |layer|
{
  if |layer| == 2 then
    [HashCombine(layer[0], layer[1])]
  else if |layer| % 2 == 0 then
    [HashCombine(layer[0], layer[1])] + ComputeNextLayer(layer[2..])
  else
    // Odd number: pair up all but last, then hash last with 0
    [HashCombine(layer[0], layer[1])] + ComputeNextLayerOdd(layer[2..])
}

function ComputeNextLayerOdd(layer: seq<int>): seq<int>
  requires |layer| >= 1
  decreases |layer|
{
  if |layer| == 1 then
    [HashCombine(layer[0], 0)]
  else if |layer| == 2 then
    [HashCombine(layer[0], layer[1])]
  else
    [HashCombine(layer[0], layer[1])] + ComputeNextLayerOdd(layer[2..])
}

// The full Merkle tree specification
ghost predicate ValidMerkleTree(leaves: seq<int>, tree: seq<seq<int>>)
{
  |leaves| >= 1 &&
  |tree| >= 1 &&
  // First layer is the hashed leaves
  |tree[0]| == |leaves| &&
  (forall i :: 0 <= i < |leaves| ==> tree[0][i] == HashLeaf(leaves[i])) &&
  // Last layer is the root (single element)
  |tree[|tree|-1]| == 1 &&
  // Each subsequent layer is computed from the previous
  (forall k :: 0 <= k < |tree| - 1 ==>
    |tree[k]| >= 2 &&
    tree[k+1] == ComputeLayer(tree[k]))
}

// Wrapper for computing a layer (handling length >= 2)
function ComputeLayer(layer: seq<int>): seq<int>
  requires |layer| >= 2
{
  ComputeNextLayer(layer)
}

// A Merkle proof for leaf at index `leafIdx`:
// proof[k] is the sibling hash at level k, and `directions[k]` says
// whether the sibling is on the left (true) or right (false)
ghost predicate ValidMerkleProof(
  root: int,
  leafHash: int,
  proof: seq<int>,
  directions: seq<bool>
)
{
  |proof| == |directions| &&
  ComputeProofRoot(leafHash, proof, directions) == root
}

// Compute the root from a leaf hash and a proof
function ComputeProofRoot(current: int, proof: seq<int>, directions: seq<bool>): int
  requires |proof| == |directions|
  decreases |proof|
{
  if |proof| == 0 then current
  else
    var combined := if directions[0] then HashCombine(proof[0], current)
                    else HashCombine(current, proof[0]);
    ComputeProofRoot(combined, proof[1..], directions[1..])
}

// The full spec: build tree and verify proof
ghost predicate MerkleSpec(
  leaves: seq<int>,
  tree: seq<seq<int>>,
  leafIdx: int,
  proof: seq<int>,
  directions: seq<bool>
)
{
  |leaves| >= 2 &&
  0 <= leafIdx < |leaves| &&
  ValidMerkleTree(leaves, tree) &&
  |proof| == |tree| - 1 &&
  |directions| == |proof| &&
  ValidMerkleProof(tree[|tree|-1][0], HashLeaf(leaves[leafIdx]), proof, directions)
}

// Build the Merkle tree from leaves
method BuildMerkleTree(leaves: seq<int>) returns (tree: seq<seq<int>>)
  requires |leaves| >= 2
  ensures ValidMerkleTree(leaves, tree)
{
  // Hash the leaves
  var leafLayer: seq<int> := [];
  var i := 0;
  while i < |leaves|
    // INVARIANT NEEDED HERE
  {
    leafLayer := leafLayer + [HashLeaf(leaves[i])];
    i := i + 1;
  }

  tree := [leafLayer];
  var currentLayer := leafLayer;

  // Build layers until we reach the root
  while |currentLayer| >= 2
    // INVARIANT NEEDED HERE
  {
    var nextLayer := ComputeLayerImpl(currentLayer);
    tree := tree + [nextLayer];
    currentLayer := nextLayer;
  }
}

// Imperative implementation of ComputeLayer
method ComputeLayerImpl(layer: seq<int>) returns (result: seq<int>)
  requires |layer| >= 2
  ensures result == ComputeLayer(layer)
{
  result := [];
  var i := 0;
  while i < |layer|
    // INVARIANT NEEDED HERE
  {
    if i + 1 < |layer| {
      result := result + [HashCombine(layer[i], layer[i+1])];
      i := i + 2;
    } else {
      // Odd element at end: pair with 0
      result := result + [HashCombine(layer[i], 0)];
      i := i + 1;
    }
  }
}

// Extract a Merkle proof for a given leaf index
method ExtractProof(tree: seq<seq<int>>, leafIdx: int)
  returns (proof: seq<int>, directions: seq<bool>)
  requires |tree| >= 2
  requires ValidMerkleTree2(tree)
  requires 0 <= leafIdx < |tree[0]|
  ensures |proof| == |tree| - 1
  ensures |directions| == |proof|
  ensures ValidMerkleProof(tree[|tree|-1][0], tree[0][leafIdx], proof, directions)
{
  proof := [];
  directions := [];
  var idx := leafIdx;
  var level := 0;

  while level < |tree| - 1
    // INVARIANT NEEDED HERE
  {
    var layer := tree[level];
    var siblingIdx: int;
    var dir: bool;
    if idx % 2 == 0 {
      // Current node is left child, sibling is right
      if idx + 1 < |layer| {
        siblingIdx := idx + 1;
      } else {
        siblingIdx := -1; // no sibling, use 0
      }
      dir := false;
    } else {
      // Current node is right child, sibling is left
      siblingIdx := idx - 1;
      dir := true;
    }

    var siblingHash: int;
    if siblingIdx >= 0 && siblingIdx < |layer| {
      siblingHash := layer[siblingIdx];
    } else {
      siblingHash := 0;
    }

    proof := proof + [siblingHash];
    directions := directions + [dir];
    idx := idx / 2;
    level := level + 1;
  }
}

// Helper predicate for tree structure (without leaf relationship)
ghost predicate ValidMerkleTree2(tree: seq<seq<int>>)
{
  |tree| >= 1 &&
  |tree[|tree|-1]| == 1 &&
  (forall k :: 0 <= k < |tree| - 1 ==>
    |tree[k]| >= 2 &&
    tree[k+1] == ComputeLayer(tree[k]))
}

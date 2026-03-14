/*
 * Tests for Problem 6: Merkle Tree Construction and Proof Verification
 *
 * We test the spec predicates on small concrete examples, manually computing
 * hash values and verifying Merkle proofs.
 */

function HashCombine(left: int, right: int): int
{
  ((left * 31 + right * 37 + 7) % 1000000007)
}

function HashLeaf(v: int): int
{
  ((v * 53 + 13) % 1000000007)
}

function ComputeNextLayer(layer: seq<int>): seq<int>
  requires |layer| >= 2
  decreases |layer|
{
  if |layer| == 2 then
    [HashCombine(layer[0], layer[1])]
  else if |layer| % 2 == 0 then
    [HashCombine(layer[0], layer[1])] + ComputeNextLayer(layer[2..])
  else
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

function ComputeLayer(layer: seq<int>): seq<int>
  requires |layer| >= 2
{
  ComputeNextLayer(layer)
}

ghost predicate ValidMerkleTree(leaves: seq<int>, tree: seq<seq<int>>)
{
  |leaves| >= 1 &&
  |tree| >= 1 &&
  |tree[0]| == |leaves| &&
  (forall i :: 0 <= i < |leaves| ==> tree[0][i] == HashLeaf(leaves[i])) &&
  |tree[|tree|-1]| == 1 &&
  (forall k :: 0 <= k < |tree| - 1 ==>
    |tree[k]| >= 2 &&
    tree[k+1] == ComputeLayer(tree[k]))
}

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

// Test 1: Two leaves [10, 20]
// Layer 0: [HashLeaf(10), HashLeaf(20)]
// Layer 1: [HashCombine(HashLeaf(10), HashLeaf(20))]
method test1()
{
  var h0 := HashLeaf(10);  // (10*53+13) % 1000000007 = 543
  var h1 := HashLeaf(20);  // (20*53+13) % 1000000007 = 1073
  assert h0 == 543;
  assert h1 == 1073;

  var root := HashCombine(h0, h1);
  // (543*31 + 1073*37 + 7) % 1000000007 = 16833 + 39701 + 7 = 56541
  assert root == 56541;

  var tree: seq<seq<int>> := [[h0, h1], [root]];
  var leaves := [10, 20];

  assert tree[0] == [h0, h1];
  assert tree[1] == [root];
  assert |tree| == 2;
  assert |tree[|tree|-1]| == 1;
  assert tree[0][0] == HashLeaf(10);
  assert tree[0][1] == HashLeaf(20);

  // tree[1] == ComputeLayer(tree[0])
  assert ComputeNextLayer([h0, h1]) == [HashCombine(h0, h1)];
  assert ComputeLayer(tree[0]) == [root];
  assert tree[1] == ComputeLayer(tree[0]);

  assert ValidMerkleTree(leaves, tree);
}

// Test 2: Merkle proof for leaf 0 in a 2-leaf tree
method test2()
{
  var h0 := HashLeaf(10);
  var h1 := HashLeaf(20);
  var root := HashCombine(h0, h1);

  assert h0 == 543;
  assert h1 == 1073;
  assert root == 56541;

  // Proof for leaf 0: sibling is h1, direction is false (sibling on right)
  var proof := [h1];
  var directions := [false];

  // ComputeProofRoot(h0, [h1], [false])
  // = ComputeProofRoot(HashCombine(h0, h1), [], [])
  // = HashCombine(h0, h1) = root
  assert proof[1..] == [];
  assert directions[1..] == [];
  assert ComputeProofRoot(h0, proof, directions) == root;
  assert ValidMerkleProof(root, h0, proof, directions);

  var leaves := [10, 20];
  var tree: seq<seq<int>> := [[h0, h1], [root]];
  assert ComputeLayer(tree[0]) == [root];
  assert ValidMerkleTree(leaves, tree);
  assert MerkleSpec(leaves, tree, 0, proof, directions);
}

// Test 3: Merkle proof for leaf 1 in a 2-leaf tree
method test3()
{
  var h0 := HashLeaf(10);
  var h1 := HashLeaf(20);
  var root := HashCombine(h0, h1);

  assert h0 == 543;
  assert h1 == 1073;
  assert root == 56541;

  // Proof for leaf 1: sibling is h0, direction is true (sibling on left)
  var proof := [h0];
  var directions := [true];

  // ComputeProofRoot(h1, [h0], [true])
  // = ComputeProofRoot(HashCombine(h0, h1), [], [])
  // = root
  assert proof[1..] == [];
  assert directions[1..] == [];
  var combined := HashCombine(h0, h1);
  assert combined == root;
  assert ComputeProofRoot(h1, proof, directions) == root;
  assert ValidMerkleProof(root, h1, proof, directions);

  var leaves := [10, 20];
  var tree: seq<seq<int>> := [[h0, h1], [root]];
  assert ComputeLayer(tree[0]) == [root];
  assert ValidMerkleTree(leaves, tree);
  assert MerkleSpec(leaves, tree, 1, proof, directions);
}

// Test 4: Four leaves, proof for leaf 2
method test4()
{
  var h0 := HashLeaf(1);  // (1*53+13) % 1e9+7 = 66
  var h1 := HashLeaf(2);  // (2*53+13) % 1e9+7 = 119
  var h2 := HashLeaf(3);  // (3*53+13) % 1e9+7 = 172
  var h3 := HashLeaf(4);  // (4*53+13) % 1e9+7 = 225
  assert h0 == 66;
  assert h1 == 119;
  assert h2 == 172;
  assert h3 == 225;

  // Layer 1: [HashCombine(h0,h1), HashCombine(h2,h3)]
  var n0 := HashCombine(h0, h1);
  // 66*31 + 119*37 + 7 = 2046 + 4403 + 7 = 6456
  assert n0 == 6456;
  var n1 := HashCombine(h2, h3);
  // 172*31 + 225*37 + 7 = 5332 + 8325 + 7 = 13664
  assert n1 == 13664;

  // Layer 2: [HashCombine(n0, n1)]
  var root := HashCombine(n0, n1);
  // 6456*31 + 13664*37 + 7 = 200136 + 505568 + 7 = 705711
  assert root == 705711;

  var layer0 := [h0, h1, h2, h3];
  var layer1 := [n0, n1];
  var layer2 := [root];

  // Verify layer computation
  assert layer0[2..] == [h2, h3];
  assert ComputeNextLayer(layer0[2..]) == [HashCombine(h2, h3)];
  assert ComputeNextLayer(layer0) == [HashCombine(h0, h1)] + ComputeNextLayer(layer0[2..]);
  assert ComputeLayer(layer0) == [n0, n1];
  assert ComputeLayer(layer1) == [root];

  var tree := [layer0, layer1, layer2];
  var leaves := [1, 2, 3, 4];

  assert tree[0] == layer0;
  assert tree[1] == layer1;
  assert tree[2] == layer2;
  assert tree[1] == ComputeLayer(tree[0]);
  assert tree[2] == ComputeLayer(tree[1]);
  assert ValidMerkleTree(leaves, tree);

  // Proof for leaf 2 (h2):
  // Level 0: leaf 2's sibling is leaf 3 (h3), direction = false (sibling right)
  // Level 1: node n1's sibling is n0, direction = true (sibling left)
  var proof := [h3, n0];
  var directions := [false, true];

  // Verify:
  // ComputeProofRoot(h2, [h3, n0], [false, true])
  //   combined = HashCombine(h2, h3) = n1
  //   ComputeProofRoot(n1, [n0], [true])
  //     combined = HashCombine(n0, n1) = root
  //     ComputeProofRoot(root, [], []) = root
  assert proof[1..] == [n0];
  assert directions[1..] == [true];
  assert [n0][1..] == [];
  assert [true][1..] == [];

  var step1 := HashCombine(h2, h3);
  assert step1 == n1;
  var step2 := HashCombine(n0, n1);
  assert step2 == root;
  assert ComputeProofRoot(n1, [n0], [true]) == root;
  assert ComputeProofRoot(h2, proof, directions) == root;
  assert ValidMerkleProof(root, h2, proof, directions);

  assert MerkleSpec(leaves, tree, 2, proof, directions);
}

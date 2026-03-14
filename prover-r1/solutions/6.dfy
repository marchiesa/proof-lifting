/*
 * Problem 6: Merkle Tree Construction and Proof Verification
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

function ComputeLayer(layer: seq<int>): seq<int>
  requires |layer| >= 2
{
  ComputeNextLayer(layer)
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

ghost predicate ValidMerkleTree2(tree: seq<seq<int>>)
{
  |tree| >= 1 &&
  |tree[|tree|-1]| == 1 &&
  (forall k :: 0 <= k < |tree| - 1 ==>
    |tree[k]| >= 2 &&
    tree[k+1] == ComputeLayer(tree[k]))
}

// ============================================================
// Length lemmas
// ============================================================

lemma ComputeNextLayerLength(layer: seq<int>)
  requires |layer| >= 2
  ensures |ComputeNextLayer(layer)| == (|layer| + 1) / 2
  ensures |ComputeNextLayer(layer)| >= 1
  ensures |ComputeNextLayer(layer)| < |layer|
  decreases |layer|
{
  if |layer| == 2 {
  } else if |layer| % 2 == 0 {
    ComputeNextLayerLength(layer[2..]);
  } else {
    ComputeNextLayerOddLength(layer[2..]);
  }
}

lemma ComputeNextLayerOddLength(layer: seq<int>)
  requires |layer| >= 1
  ensures |ComputeNextLayerOdd(layer)| == (|layer| + 1) / 2
  decreases |layer|
{
  if |layer| == 1 {
  } else if |layer| == 2 {
  } else {
    ComputeNextLayerOddLength(layer[2..]);
  }
}

// ============================================================
// ComputeLayerImpl
// ============================================================

// Define what the iterative computation from index i onward should produce
function IterResult(layer: seq<int>, i: int): seq<int>
  requires 0 <= i <= |layer|
  requires i % 2 == 0 || i == |layer|
  decreases |layer| - i
{
  if i >= |layer| then []
  else if i + 1 >= |layer| then [HashCombine(layer[i], 0)]
  else [HashCombine(layer[i], layer[i+1])] + IterResult(layer, i + 2)
}

// IterResult(layer, 0) == ComputeNextLayer(layer) for |layer| >= 2
lemma IterResultIsComputeNextLayer(layer: seq<int>)
  requires |layer| >= 2
  ensures IterResult(layer, 0) == ComputeNextLayer(layer)
{
  IterResultMatchesRecursive(layer, 0, |layer|);
}

// Helper: show IterResult matches the recursive functions
lemma IterResultMatchesRecursive(layer: seq<int>, i: int, remaining: int)
  requires |layer| >= 2
  requires 0 <= i <= |layer|
  requires i % 2 == 0
  requires remaining == |layer| - i
  ensures remaining >= 2 && remaining % 2 == 0 ==>
    IterResult(layer, i) == ComputeNextLayer(layer[i..])
  ensures remaining >= 2 && remaining % 2 == 1 ==>
    IterResult(layer, i) == ComputeNextLayer(layer[i..])
  ensures remaining == 1 ==>
    IterResult(layer, i) == [HashCombine(layer[i], 0)]
  ensures remaining == 0 ==>
    IterResult(layer, i) == []
  decreases remaining
{
  if remaining == 0 || remaining == 1 {
    // Base cases
  } else if remaining == 2 {
    assert layer[i..] == [layer[i], layer[i+1]];
    assert ComputeNextLayer(layer[i..]) == [HashCombine(layer[i], layer[i+1])];
    assert IterResult(layer, i) == [HashCombine(layer[i], layer[i+1])] + IterResult(layer, i+2);
    assert IterResult(layer, i+2) == [];
  } else {
    // remaining >= 3
    var sub := layer[i..];
    assert |sub| >= 3;
    assert sub[0] == layer[i];
    assert sub[1] == layer[i+1];
    assert sub[2..] == layer[i+2..];

    assert IterResult(layer, i) == [HashCombine(layer[i], layer[i+1])] + IterResult(layer, i+2);

    if |sub| % 2 == 0 {
      // Even case
      assert ComputeNextLayer(sub) == [HashCombine(sub[0], sub[1])] + ComputeNextLayer(sub[2..]);
      IterResultMatchesRecursive(layer, i+2, remaining - 2);
      // remaining - 2 >= 2 and (remaining-2) % 2 == 0
      assert IterResult(layer, i+2) == ComputeNextLayer(layer[i+2..]);
    } else {
      // Odd case
      assert ComputeNextLayer(sub) == [HashCombine(sub[0], sub[1])] + ComputeNextLayerOdd(sub[2..]);
      // IterResult(layer, i+2) should equal ComputeNextLayerOdd(sub[2..])
      // sub[2..] has odd-2 elements (which is even since sub is odd), oh wait...
      // |sub| is odd >= 3, so |sub[2..]| = |sub| - 2 is odd-2 (which is also odd if |sub| is odd)
      // Wait: odd - 2 = odd. So |sub[2..]| is odd, >= 1.
      IterResultMatchesOdd(layer, i+2, remaining - 2);
    }
  }
}

lemma IterResultMatchesOdd(layer: seq<int>, i: int, remaining: int)
  requires |layer| >= 2
  requires 0 <= i <= |layer|
  requires i % 2 == 0
  requires remaining == |layer| - i
  requires remaining >= 1
  requires remaining % 2 == 1
  ensures IterResult(layer, i) == ComputeNextLayerOdd(layer[i..])
  decreases remaining
{
  var sub := layer[i..];
  if remaining == 1 {
    assert |sub| == 1;
    assert IterResult(layer, i) == [HashCombine(layer[i], 0)];
    assert ComputeNextLayerOdd(sub) == [HashCombine(sub[0], 0)];
    assert sub[0] == layer[i];
  } else if remaining == 2 {
    // Can't happen: remaining is odd
    assert false;
  } else {
    // remaining >= 3 and odd
    assert |sub| >= 3;
    if |sub| == 2 {
      assert false; // |sub| == remaining >= 3
    }
    assert ComputeNextLayerOdd(sub) == [HashCombine(sub[0], sub[1])] + ComputeNextLayerOdd(sub[2..]);
    assert IterResult(layer, i) == [HashCombine(layer[i], layer[i+1])] + IterResult(layer, i+2);
    assert sub[0] == layer[i];
    assert sub[1] == layer[i+1];
    assert sub[2..] == layer[i+2..];
    // remaining - 2 is odd - 2, which is odd >= 1
    IterResultMatchesOdd(layer, i+2, remaining - 2);
  }
}

method ComputeLayerImpl(layer: seq<int>) returns (result: seq<int>)
  requires |layer| >= 2
  ensures result == ComputeLayer(layer)
{
  IterResultIsComputeNextLayer(layer);

  result := [];
  var i := 0;
  while i < |layer|
    invariant 0 <= i <= |layer|
    invariant i % 2 == 0 || i == |layer|
    invariant result + IterResult(layer, i) == IterResult(layer, 0)
  {
    if i + 1 < |layer| {
      result := result + [HashCombine(layer[i], layer[i+1])];
      i := i + 2;
    } else {
      result := result + [HashCombine(layer[i], 0)];
      i := i + 1;
    }
  }
  // IterResult(layer, |layer|) == []
  // So result == IterResult(layer, 0) == ComputeNextLayer(layer) == ComputeLayer(layer)
}

// ============================================================
// BuildMerkleTree
// ============================================================

method BuildMerkleTree(leaves: seq<int>) returns (tree: seq<seq<int>>)
  requires |leaves| >= 2
  ensures ValidMerkleTree(leaves, tree)
{
  var leafLayer: seq<int> := [];
  var i := 0;
  while i < |leaves|
    invariant 0 <= i <= |leaves|
    invariant |leafLayer| == i
    invariant forall j :: 0 <= j < i ==> leafLayer[j] == HashLeaf(leaves[j])
  {
    leafLayer := leafLayer + [HashLeaf(leaves[i])];
    i := i + 1;
  }

  tree := [leafLayer];
  var currentLayer := leafLayer;

  while |currentLayer| >= 2
    invariant |tree| >= 1
    invariant tree[|tree|-1] == currentLayer
    invariant |currentLayer| >= 1
    invariant |tree[0]| == |leaves|
    invariant forall j :: 0 <= j < |leaves| ==> tree[0][j] == HashLeaf(leaves[j])
    invariant forall k :: 0 <= k < |tree| - 1 ==>
      |tree[k]| >= 2 && tree[k+1] == ComputeLayer(tree[k])
    decreases |currentLayer|
  {
    ComputeNextLayerLength(currentLayer);
    var nextLayer := ComputeLayerImpl(currentLayer);
    tree := tree + [nextLayer];
    currentLayer := nextLayer;
  }

  assert |currentLayer| == 1;
}

// ============================================================
// ExtractProof
// ============================================================

// Lemma: appending a proof step
lemma ComputeProofRootAppend(leafHash: int, proof: seq<int>, dirs: seq<bool>, sibling: int, dir: bool)
  requires |proof| == |dirs|
  ensures ComputeProofRoot(leafHash, proof + [sibling], dirs + [dir]) ==
    (if dir then HashCombine(sibling, ComputeProofRoot(leafHash, proof, dirs))
     else HashCombine(ComputeProofRoot(leafHash, proof, dirs), sibling))
  decreases |proof|
{
  if |proof| == 0 {
    assert proof + [sibling] == [sibling];
    assert dirs + [dir] == [dir];
  } else {
    var combined := if dirs[0] then HashCombine(proof[0], leafHash) else HashCombine(leafHash, proof[0]);
    assert (proof + [sibling])[0] == proof[0];
    assert (dirs + [dir])[0] == dirs[0];
    assert (proof + [sibling])[1..] == proof[1..] + [sibling];
    assert (dirs + [dir])[1..] == dirs[1..] + [dir];
    ComputeProofRootAppend(combined, proof[1..], dirs[1..], sibling, dir);
  }
}

// Lemma: element at position idx/2 in the next layer
lemma {:isolate_assertions} ComputeNextLayerIndex(layer: seq<int>, pairIdx: int)
  requires |layer| >= 2
  requires 0 <= pairIdx
  requires pairIdx * 2 < |layer|
  ensures pairIdx < |ComputeNextLayer(layer)|
  ensures pairIdx * 2 + 1 < |layer| ==>
    ComputeNextLayer(layer)[pairIdx] == HashCombine(layer[pairIdx * 2], layer[pairIdx * 2 + 1])
  ensures pairIdx * 2 + 1 >= |layer| ==>
    ComputeNextLayer(layer)[pairIdx] == HashCombine(layer[pairIdx * 2], 0)
  decreases |layer|
{
  ComputeNextLayerLength(layer);
  if pairIdx == 0 {
    if |layer| == 2 {
    } else if |layer| % 2 == 0 {
      assert ComputeNextLayer(layer) == [HashCombine(layer[0], layer[1])] + ComputeNextLayer(layer[2..]);
    } else {
      assert ComputeNextLayer(layer) == [HashCombine(layer[0], layer[1])] + ComputeNextLayerOdd(layer[2..]);
    }
  } else {
    // pairIdx >= 1, so |layer| >= 4
    if |layer| % 2 == 0 {
      assert ComputeNextLayer(layer) == [HashCombine(layer[0], layer[1])] + ComputeNextLayer(layer[2..]);
      assert layer[2..][0] == layer[2];
      ComputeNextLayerIndex(layer[2..], pairIdx - 1);
      assert ComputeNextLayer(layer)[pairIdx] == ComputeNextLayer(layer[2..])[pairIdx - 1];
      assert layer[2..][(pairIdx-1)*2] == layer[pairIdx*2];
      if (pairIdx-1)*2 + 1 < |layer[2..]| {
        assert layer[2..][(pairIdx-1)*2+1] == layer[pairIdx*2+1];
      }
    } else {
      assert ComputeNextLayer(layer) == [HashCombine(layer[0], layer[1])] + ComputeNextLayerOdd(layer[2..]);
      ComputeNextLayerOddIndex(layer[2..], pairIdx - 1);
      assert ComputeNextLayer(layer)[pairIdx] == ComputeNextLayerOdd(layer[2..])[pairIdx - 1];
      assert layer[2..][(pairIdx-1)*2] == layer[pairIdx*2];
      if (pairIdx-1)*2 + 1 < |layer[2..]| {
        assert layer[2..][(pairIdx-1)*2+1] == layer[pairIdx*2+1];
      }
    }
  }
}

lemma {:isolate_assertions} ComputeNextLayerOddIndex(layer: seq<int>, pairIdx: int)
  requires |layer| >= 1
  requires 0 <= pairIdx
  requires pairIdx * 2 < |layer|
  ensures pairIdx < |ComputeNextLayerOdd(layer)|
  ensures pairIdx * 2 + 1 < |layer| ==>
    ComputeNextLayerOdd(layer)[pairIdx] == HashCombine(layer[pairIdx * 2], layer[pairIdx * 2 + 1])
  ensures pairIdx * 2 + 1 >= |layer| ==>
    ComputeNextLayerOdd(layer)[pairIdx] == HashCombine(layer[pairIdx * 2], 0)
  decreases |layer|
{
  ComputeNextLayerOddLength(layer);
  if pairIdx == 0 {
    if |layer| == 1 {
    } else if |layer| == 2 {
    } else {
      assert ComputeNextLayerOdd(layer) == [HashCombine(layer[0], layer[1])] + ComputeNextLayerOdd(layer[2..]);
    }
  } else {
    // pairIdx >= 1
    if |layer| <= 2 {
      // pairIdx >= 1 but |layer| <= 2 means pairIdx*2 >= 2 > |layer|, contradiction
      assert false;
    }
    assert ComputeNextLayerOdd(layer) == [HashCombine(layer[0], layer[1])] + ComputeNextLayerOdd(layer[2..]);
    ComputeNextLayerOddIndex(layer[2..], pairIdx - 1);
    assert ComputeNextLayerOdd(layer)[pairIdx] == ComputeNextLayerOdd(layer[2..])[pairIdx - 1];
    assert layer[2..][(pairIdx-1)*2] == layer[pairIdx*2];
    if (pairIdx-1)*2 + 1 < |layer[2..]| {
      assert layer[2..][(pairIdx-1)*2+1] == layer[pairIdx*2+1];
    }
  }
}

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
    invariant 0 <= level <= |tree| - 1
    invariant |proof| == level
    invariant |directions| == level
    invariant 0 <= idx < |tree[level]|
    invariant ComputeProofRoot(tree[0][leafIdx], proof, directions) == tree[level][idx]
  {
    var layer := tree[level];
    assert |layer| >= 2;
    assert tree[level+1] == ComputeLayer(tree[level]);

    var pairIdx := idx / 2;
    ComputeNextLayerLength(layer);
    ComputeNextLayerIndex(layer, pairIdx);
    assert pairIdx < |ComputeNextLayer(layer)|;

    var siblingIdx: int;
    var dir: bool;
    if idx % 2 == 0 {
      if idx + 1 < |layer| {
        siblingIdx := idx + 1;
      } else {
        siblingIdx := -1;
      }
      dir := false;
    } else {
      siblingIdx := idx - 1;
      dir := true;
    }

    var siblingHash: int;
    if siblingIdx >= 0 && siblingIdx < |layer| {
      siblingHash := layer[siblingIdx];
    } else {
      siblingHash := 0;
    }

    // Show that the combined hash matches tree[level+1][pairIdx]
    ComputeProofRootAppend(tree[0][leafIdx], proof, directions, siblingHash, dir);

    assert ComputeProofRoot(tree[0][leafIdx], proof + [siblingHash], directions + [dir]) ==
      tree[level+1][pairIdx] by {
      if idx % 2 == 0 {
        assert dir == false;
        if idx + 1 < |layer| {
          assert siblingHash == layer[idx + 1];
          assert tree[level+1][pairIdx] == HashCombine(layer[idx], layer[idx+1]);
          assert HashCombine(tree[level][idx], siblingHash) == HashCombine(layer[idx], layer[idx+1]);
        } else {
          assert siblingHash == 0;
          assert tree[level+1][pairIdx] == HashCombine(layer[idx], 0);
        }
      } else {
        assert dir == true;
        assert siblingHash == layer[idx - 1];
        // pairIdx == idx / 2 == (idx-1) / 2 (since idx is odd)
        assert pairIdx * 2 == idx - 1;
        assert pairIdx * 2 + 1 == idx;
        assert pairIdx * 2 + 1 < |layer|;
        assert tree[level+1][pairIdx] == HashCombine(layer[pairIdx*2], layer[pairIdx*2+1]);
        assert layer[pairIdx*2] == layer[idx-1] == siblingHash;
        assert layer[pairIdx*2+1] == layer[idx] == tree[level][idx];
        assert HashCombine(siblingHash, tree[level][idx]) == HashCombine(layer[idx-1], layer[idx]);
      }
    }

    proof := proof + [siblingHash];
    directions := directions + [dir];
    idx := idx / 2;
    level := level + 1;
  }
}

ghost predicate InSeq(x: int, s: seq<int>)
{
  exists i | 0 <= i < |s| :: s[i] == x
}

ghost predicate ValidChoice(a: int, b: int, A: seq<int>, B: seq<int>)
{
  InSeq(a, A) && InSeq(b, B) && !InSeq(a + b, A) && !InSeq(a + b, B)
}

lemma InSeqMultiset(x: int, s: seq<int>)
  ensures InSeq(x, s) <==> x in multiset(s)
{
  if |s| == 0 {
  } else {
    InSeqMultiset(x, s[1..]);
    assert s == [s[0]] + s[1..];
  }
}


lemma ElementBounded(sorted: seq<int>, orig: seq<int>, bound: int)
  requires multiset(sorted) == multiset(orig)
  requires forall k | 0 <= k < |sorted| :: sorted[k] <= bound
  ensures forall k | 0 <= k < |orig| :: orig[k] <= bound
{
  forall k | 0 <= k < |orig|
    ensures orig[k] <= bound
  {


  var sortedA := A;
  var sortedB := B;

  var i := 0;
  while i < |sortedA|
    invariant 0 <= i <= |sortedA|
    invariant |sortedA| == |A|
    invariant multiset(sortedA) == multiset(A)
    invariant forall p | 0 <= p < i :: forall q | p < q < |sortedA| :: sortedA[p] <= sortedA[q]
  {
    var j := i + 1;
    while j < |sortedA|
      invariant i + 1 <= j <= |sortedA|
      invariant |sortedA| == |A|
      invariant multiset(sortedA) == multiset(A)
      invariant forall p | 0 <= p < i :: forall q | p < q < |sortedA| :: sortedA[p] <= sortedA[q]
      invariant forall k | i < k < j :: sortedA[i] <= sortedA[k]
    {
      if sortedA[j] < sortedA[i]
      {
        var tmp := sortedA[i];
        sortedA := sortedA[i := sortedA[j]];
        sortedA := sortedA[j := tmp];
      }
      j := j + 1;
    }
    i := i + 1;
  }

  i := 0;
  while i < |sortedB|
    invariant 0 <= i <= |sortedB|
    invariant |sortedB| == |B|
    invariant multiset(sortedB) == multiset(B)
    invariant forall p | 0 <= p < i :: forall q | p < q < |sortedB| :: sortedB[p] <= sortedB[q]
  {
    var j := i + 1;
    while j < |sortedB|
      invariant i + 1 <= j <= |sortedB|
      invariant |sortedB| == |B|
      invariant multiset(sortedB) == multiset(B)
      invariant forall p | 0 <= p < i :: forall q | p < q < |sortedB| :: sortedB[p] <= sortedB[q]
      invariant forall k | i < k < j :: sortedB[i] <= sortedB[k]
    {
      if sortedB[j] < sortedB[i]
      {
        var tmp := sortedB[i];
        sortedB := sortedB[i := sortedB[j]];
        sortedB := sortedB[j := tmp];
      }
      j := j + 1;
    }
    i := i + 1;
  }

  a := sortedA[|sortedA| - 1];
  b := sortedB[|sortedB| - 1];

  // Prove a is in A
  assert InSeq(a, sortedA) by {
    assert 0 <= |sortedA| - 1 < |sortedA|;
    assert sortedA[|sortedA| - 1] == a;
  }
  // Inlined from PermutationInSeq(a, sortedA, A)
  InSeqMultiset((a), (sortedA));
  InSeqMultiset((a), (A));
  assert InSeq(a, A);

  // Prove b is in B
  assert InSeq(b, sortedB) by {
    assert 0 <= |sortedB| - 1 < |sortedB|;
    assert sortedB[|sortedB| - 1] == b;
  }
  // Inlined from PermutationInSeq(b, sortedB, B)
  InSeqMultiset((b), (sortedB));
  InSeqMultiset((b), (B));
  assert InSeq(b, B);

  // a is max of sortedA, b is max of sortedB
  assert forall k | 0 <= k < |sortedA| :: sortedA[k] <= a;
  assert forall k | 0 <= k < |sortedB| :: sortedB[k] <= b;

  // All elements of A are <= a, all elements of B are <= b
  // Inlined from ElementBounded(sortedA, A, a)
  forall k | 0 <= k < |(A)|
  ensures (A)[k] <= (a)
  {
  assert (A)[k] in multiset((A));
  assert (A)[k] in multiset((sortedA));
  InSeqMultiset((A)[k], (sortedA));
  var j :| 0 <= j < |(sortedA)| && (sortedA)[j] == (A)[k];
  }
  assert A[k] <= a;
  // Inlined from ElementBounded(sortedB, B, b)
  forall k | 0 <= k < |(B)|
  ensures (B)[k] <= (b)
  {
  assert (B)[k] in multiset((B));
  assert (B)[k] in multiset((sortedB));
  InSeqMultiset((B)[k], (sortedB));
  var j :| 0 <= j < |(sortedB)| && (sortedB)[j] == (B)[k];
  }
  assert B[k] <= b;

  // a > 0 and b > 0
  assert InSeq(a, A);
  var idxA :| 0 <= idxA < |A| && A[idxA] == a;
  assert a > 0;

  assert InSeq(b, B);
  var idxB :| 0 <= idxB < |B| && B[idxB] == b;
  assert b > 0;

  // a + b > every element of A and B
  assert forall k | 0 <= k < |A| :: A[k] < a + b;
  assert forall k | 0 <= k < |B| :: B[k] < a + b;

  // Therefore a + b not in A or B
  assert !InSeq(a + b, A) by {
    if InSeq(a + b, A) {
      var k :| 0 <= k < |A| && A[k] == a + b;
      assert A[k] < a + b;
    }
  }
  assert !InSeq(a + b, B) by {
    if InSeq(a + b, B) {
      var k :| 0 <= k < |B| && B[k] == a + b;
      assert B[k] < a + b;
    }
  }
}

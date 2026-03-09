// Test file for AstMappingManager - demonstrates tracking of:
// - Functions
// - Lemmas (with recursive calls)
// - Loop invariants
// - Assertions
// - Requires/Ensures
// - Lemma calls from methods
//
// Verified: 12 verified, 0 errors

function Sum(s: seq<int>): int
{
  if |s| == 0 then 0
  else Sum(s[..|s|-1]) + s[|s|-1]
}

// Lemma: Sum of concatenation
lemma SumConcat(s1: seq<int>, s2: seq<int>)
  ensures Sum(s1 + s2) == Sum(s1) + Sum(s2)
{
  if |s2| == 0 {
    assert s1 + s2 == s1;
  } else {
    SumConcat(s1, s2[..|s2|-1]);
    assert (s1 + s2)[..|s1 + s2|-1] == s1 + s2[..|s2|-1];
  }
}

// Lemma: Slice extension property
lemma SliceExtend(s: seq<int>, i: int)
  requires 0 <= i < |s|
  ensures Sum(s[..i+1]) == Sum(s[..i]) + s[i]
{
  assert s[..i+1] == s[..i] + [s[i]];
  SumConcat(s[..i], [s[i]]);
}

// Lemma: Full slice equals sequence
lemma FullSlice(s: seq<int>)
  ensures s[..|s|] == s
{
  // trivial
}

// Lemma about sum being additive for splitting
lemma SumSplit(s: seq<int>, mid: int)
  requires 0 <= mid <= |s|
  ensures Sum(s) == Sum(s[..mid]) + Sum(s[mid..])
{
  assert s == s[..mid] + s[mid..];
  SumConcat(s[..mid], s[mid..]);
}

// Method that uses all the lemmas
method ComputeSumWithLemmas(s: seq<int>) returns (sum: int)
  requires |s| > 0
  ensures sum == Sum(s)
{
  sum := s[0];
  var i := 1;

  while i < |s|
    invariant 1 <= i <= |s|
    invariant sum == Sum(s[..i])
  {
    SliceExtend(s, i);  // Call lemma to help prove invariant maintenance
    sum := sum + s[i];
    i := i + 1;
  }

  FullSlice(s);  // Call lemma to help prove postcondition
}

// Forall statement example (forall assign - not tracked as forall proof)
method TestForall(a: array<int>)
  modifies a
  ensures forall i :: 0 <= i < a.Length ==> a[i] == 0
{
  forall i | 0 <= i < a.Length
  {
    a[i] := 0;
  }
}

// Method with nested lemma calls
method ComputeSumFromEnd(s: seq<int>) returns (sum: int)
  requires |s| > 0
  ensures sum == Sum(s)
{
  sum := s[|s|-1];
  var i := |s| - 1;

  while i > 0
    invariant 0 <= i < |s|
    invariant sum == Sum(s[i..])
  {
    i := i - 1;
    // Prove: Sum(s[i..]) == s[i] + Sum(s[i+1..])
    assert s[i..] == [s[i]] + s[i+1..];
    SumConcat([s[i]], s[i+1..]);
    sum := s[i] + sum;
  }

  assert s[0..] == s;
}

// Problem 3: Sequence Slicing Pitfalls — Merge Sorted Halves (SOLUTION)
//
// The multiset invariant:
//   multiset(result) == multiset(a[..i]) + multiset(b[..j])
// is logically correct, but Z3 cannot prove invariant maintenance without
// explicit assertions about how sequence slicing interacts with multisets.
//
// Specifically, Z3 cannot automatically derive:
//   a[..i+1] == a[..i] + [a[i]]
//   b[..j+1] == b[..j] + [b[j]]
//
// These are trivially true but Z3 needs them as explicit terms to trigger
// the multiset concatenation axioms.

predicate SortedSeq(s: seq<int>)
{
  forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j]
}

method MergeSorted(a: seq<int>, b: seq<int>) returns (result: seq<int>)
  requires SortedSeq(a)
  requires SortedSeq(b)
  ensures SortedSeq(result)
  ensures |result| == |a| + |b|
  ensures multiset(result) == multiset(a) + multiset(b)
{
  result := [];
  var i := 0;
  var j := 0;
  while i < |a| || j < |b|
    decreases |a| - i + |b| - j
    invariant 0 <= i <= |a|
    invariant 0 <= j <= |b|
    invariant |result| == i + j
    invariant SortedSeq(result)
    invariant |result| > 0 && i < |a| ==> result[|result|-1] <= a[i]
    invariant |result| > 0 && j < |b| ==> result[|result|-1] <= b[j]
    invariant multiset(result) == multiset(a[..i]) + multiset(b[..j])
  {
    if i < |a| && (j >= |b| || a[i] <= b[j]) {
      // This assertion is the fix: it gives Z3 the slice decomposition
      // that triggers the multiset axiom
      assert a[..i+1] == a[..i] + [a[i]];
      result := result + [a[i]];
      i := i + 1;
    } else {
      // Same fix for the b branch
      assert b[..j+1] == b[..j] + [b[j]];
      result := result + [b[j]];
      j := j + 1;
    }
  }
  // Final slice-to-whole assertions for the postcondition
  assert a[..|a|] == a;
  assert b[..|b|] == b;
}

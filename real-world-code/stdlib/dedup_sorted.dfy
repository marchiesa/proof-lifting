// Remove consecutive duplicates from sorted array
// (Rust: Vec::dedup, C++ std::unique, Python: itertools groupby pattern)
//
// Maintains that output is a subsequence of input with no consecutive dups.

predicate Sorted(a: seq<int>)
{
  forall i, j :: 0 <= i < j < |a| ==> a[i] <= a[j]
}

predicate NoDuplicates(a: seq<int>)
{
  forall i, j :: 0 <= i < j < |a| ==> a[i] != a[j]
}

predicate IsSubsequenceOf(sub: seq<int>, sup: seq<int>)
{
  |sub| <= |sup| &&
  exists indices: seq<int> ::
    |indices| == |sub| &&
    (forall i :: 0 <= i < |indices| ==> 0 <= indices[i] < |sup|) &&
    (forall i :: 0 <= i < |indices| ==> sub[i] == sup[indices[i]]) &&
    (forall i, j :: 0 <= i < j < |indices| ==> indices[i] < indices[j])
}

method DedupSorted(a: seq<int>) returns (result: seq<int>)
  requires Sorted(a)
  ensures Sorted(result)
  ensures NoDuplicates(result)
  ensures forall x :: x in result ==> x in a
  ensures forall x :: x in a ==> x in result
{
  if |a| == 0 { return []; }

  result := [a[0]];
  var i := 1;

  while i < |a|
    invariant 1 <= i <= |a|
    invariant |result| >= 1
    invariant Sorted(result)
    invariant NoDuplicates(result)
    invariant forall x :: x in result ==> x in a[..i]
    invariant forall x :: x in a[..i] ==> x in result
    invariant result[|result|-1] == a[i-1]
  {
    if a[i] != result[|result|-1] {
      result := result + [a[i]];
    }
    i := i + 1;
  }
}

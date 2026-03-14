// Problem 3: Sequence Slicing Pitfalls — Merge Sorted Halves

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
    invariant 0 <= i <= |a|
    invariant 0 <= j <= |b|
    invariant |result| == i + j
    invariant multiset(result) == multiset(a[..i]) + multiset(b[..j])
    invariant SortedSeq(result)
    invariant |result| > 0 && i < |a| ==> result[|result|-1] <= a[i]
    invariant |result| > 0 && j < |b| ==> result[|result|-1] <= b[j]
    decreases |a| - i + |b| - j
  {
    if i < |a| && (j >= |b| || a[i] <= b[j]) {
      assert i < |a|;
      assert |result| == 0 || result[|result|-1] <= a[i];
      result := result + [a[i]];
      i := i + 1;
      assert a[..i] == a[..i-1] + [a[i-1]];
    } else {
      assert j < |b|;
      assert |result| == 0 || result[|result|-1] <= b[j];
      result := result + [b[j]];
      j := j + 1;
      assert b[..j] == b[..j-1] + [b[j-1]];
    }
  }
  assert a[..i] == a;
  assert b[..j] == b;
}

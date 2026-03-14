// Merge Two Sorted Sequences -- Test cases

predicate IsSorted(a: seq<int>)
{
  forall i, j :: 0 <= i < j < |a| ==> a[i] <= a[j]
}

method {:axiom} MergeSorted(a: seq<int>, b: seq<int>) returns (result: seq<int>)
  requires IsSorted(a)
  requires IsSorted(b)
  ensures IsSorted(result)
  ensures |result| == |a| + |b|
  ensures multiset(result) == multiset(a) + multiset(b)

method TestMergeBasic()
{
  var a := [1, 3, 5];
  var b := [2, 4, 6];
  var r := MergeSorted(a, b);
  assert |r| == 6;
  assert IsSorted(r);
  assert 1 in multiset(r);
  assert 6 in multiset(r);
}

method TestMergeWithEmpty()
{
  var a := [1, 2];
  var b: seq<int> := [];
  var r := MergeSorted(a, b);
  assert |r| == 2;
  assert multiset(r) == multiset(a) + multiset(b);
  assert multiset(r) == multiset(a);
}

method TestBothEmpty()
{
  var a: seq<int> := [];
  var b: seq<int> := [];
  var r := MergeSorted(a, b);
  assert |r| == 0;
}

method TestMergeDuplicates()
{
  var a := [1, 1];
  var b := [1, 1];
  var r := MergeSorted(a, b);
  assert |r| == 4;
  assert IsSorted(r);
}

// Reverse a Linked List -- Reference solution with invariants

predicate IsReverse(a: seq<int>, b: seq<int>)
{
  |a| == |b| && forall i :: 0 <= i < |a| ==> a[i] == b[|b| - 1 - i]
}

method ReverseList(a: seq<int>) returns (result: seq<int>)
  ensures IsReverse(a, result)
  ensures |result| == |a|
{
  result := [];
  var i := 0;
  while i < |a|
    invariant 0 <= i <= |a|
    invariant |result| == i
    invariant forall j :: 0 <= j < i ==> result[j] == a[i - 1 - j]
    decreases |a| - i
  {
    result := [a[i]] + result;
    i := i + 1;
  }
}

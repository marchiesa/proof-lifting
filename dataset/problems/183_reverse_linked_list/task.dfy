// Reverse a Linked List (Sequence-Based)
// Task: Add loop invariants so that Dafny can verify this program.

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
  {
    result := [a[i]] + result;
    i := i + 1;
  }
}

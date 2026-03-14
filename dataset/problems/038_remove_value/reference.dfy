// Remove All Occurrences of Value from Array -- Reference solution with invariants

method RemoveValue(a: seq<int>, val: int) returns (result: seq<int>)
  ensures forall i :: 0 <= i < |result| ==> result[i] != val
  ensures forall x :: x != val ==> multiset(result)[x] == multiset(a)[x]
  ensures forall i :: 0 <= i < |result| ==> result[i] in a
{
  result := [];
  var i := 0;
  while i < |a|
    invariant 0 <= i <= |a|
    invariant forall k :: 0 <= k < |result| ==> result[k] != val
    invariant forall x :: x != val ==> multiset(result)[x] == multiset(a[..i])[x]
    invariant forall k :: 0 <= k < |result| ==> result[k] in a[..i]
    decreases |a| - i
  {
    if a[i] != val {
      result := result + [a[i]];
    }
    assert a[..i+1] == a[..i] + [a[i]];
    i := i + 1;
  }
  assert a[..|a|] == a;
}

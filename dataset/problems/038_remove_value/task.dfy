// Remove All Occurrences of Value from Array
// Task: Add loop invariants so that Dafny can verify this program.

method RemoveValue(a: seq<int>, val: int) returns (result: seq<int>)
  ensures forall i :: 0 <= i < |result| ==> result[i] != val
  ensures forall x :: x != val ==> multiset(result)[x] == multiset(a)[x]
  ensures forall i :: 0 <= i < |result| ==> result[i] in a
{
  result := [];
  var i := 0;
  while i < |a|
  {
    if a[i] != val {
      result := result + [a[i]];
    }
    i := i + 1;
  }
}

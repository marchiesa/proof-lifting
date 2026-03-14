// Array Intersection of Two Sorted Arrays
// Task: Add loop invariants so that Dafny can verify this program.

predicate IsSorted(a: seq<int>)
{
  forall i, j :: 0 <= i < j < |a| ==> a[i] <= a[j]
}

predicate StrictlySorted(a: seq<int>)
{
  forall i, j :: 0 <= i < j < |a| ==> a[i] < a[j]
}

predicate IsSubsetOf(a: seq<int>, b: seq<int>)
{
  forall x :: x in a ==> x in b
}

method Intersection(a: seq<int>, b: seq<int>) returns (result: seq<int>)
  requires StrictlySorted(a)
  requires StrictlySorted(b)
  ensures StrictlySorted(result)
  ensures IsSubsetOf(result, a)
  ensures IsSubsetOf(result, b)
  ensures forall x :: x in a && x in b ==> x in result
{
  result := [];
  var i := 0;
  var j := 0;
  while i < |a| && j < |b|
  {
    if a[i] == b[j] {
      result := result + [a[i]];
      i := i + 1;
      j := j + 1;
    } else if a[i] < b[j] {
      i := i + 1;
    } else {
      j := j + 1;
    }
  }
}

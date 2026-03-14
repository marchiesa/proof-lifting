// Find Second Maximum
// Task: Add loop invariants so that Dafny can verify this program.

predicate IsMax(val: int, s: seq<int>)
{
  forall i :: 0 <= i < |s| ==> s[i] <= val
}

predicate ExistsIn(val: int, s: seq<int>)
{
  exists i :: 0 <= i < |s| && s[i] == val
}

method SecondMax(a: seq<int>) returns (first: int, second: int)
  requires |a| >= 2
  ensures ExistsIn(first, a)
  ensures IsMax(first, a)
  ensures ExistsIn(second, a)
  ensures second <= first
  ensures forall i :: 0 <= i < |a| && a[i] != first ==> a[i] <= second
{
  first := a[0];
  second := a[1];
  if second > first {
    first, second := second, first;
  }

  var i := 2;
  while i < |a|
  {
    if a[i] > first {
      second := first;
      first := a[i];
    } else if a[i] > second {
      second := a[i];
    }
    i := i + 1;
  }
}

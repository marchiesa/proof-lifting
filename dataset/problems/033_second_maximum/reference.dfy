// Find Second Maximum -- Reference solution with invariants

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
    invariant 2 <= i <= |a|
    invariant ExistsIn(first, a[..i])
    invariant IsMax(first, a[..i])
    invariant ExistsIn(second, a[..i])
    invariant second <= first
    invariant forall k :: 0 <= k < i && a[k] != first ==> a[k] <= second
    decreases |a| - i
  {
    if a[i] > first {
      second := first;
      first := a[i];
      assert ExistsIn(first, a[..i+1]) by {
        assert a[..i+1][i] == a[i];
      }
    } else if a[i] > second {
      second := a[i];
      assert ExistsIn(second, a[..i+1]) by {
        assert a[..i+1][i] == a[i];
      }
    }
    assert a[..i+1] == a[..i] + [a[i]];
    i := i + 1;
  }
  assert a[..|a|] == a;
}

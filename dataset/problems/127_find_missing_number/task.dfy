// Find Missing Number
// Task: Add loop invariants so that Dafny can verify this program.
// Given a sequence of distinct numbers from [0..n], find one that is absent.

predicate AllInRange(a: seq<int>, n: int)
{
  forall i :: 0 <= i < |a| ==> 0 <= a[i] <= n
}

predicate AllDistinct(a: seq<int>)
{
  forall i, j :: 0 <= i < j < |a| ==> a[i] != a[j]
}

predicate Contains(a: seq<int>, v: int)
{
  exists i :: 0 <= i < |a| && a[i] == v
}

method FindMissing(a: seq<int>, n: int) returns (missing: int)
  requires n >= 0
  requires |a| == n
  requires AllInRange(a, n)
  requires AllDistinct(a)
  ensures 0 <= missing <= n
  ensures !Contains(a, missing)
{
  var m := 0;
  while m <= n
  {
    var found := false;
    var i := 0;
    while i < |a|
    {
      if a[i] == m {
        found := true;
      }
      i := i + 1;
    }
    if !found {
      return m;
    }
    m := m + 1;
  }
  return 0;
}

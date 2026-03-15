// Boats to Save People
// Task: Add loop invariants so that Dafny can verify this program.

predicate ValidWeights(weights: seq<int>, limit: int)
{
  forall i :: 0 <= i < |weights| ==> 1 <= weights[i] <= limit
}

predicate IsSorted(a: seq<int>)
{
  forall i, j :: 0 <= i < j < |a| ==> a[i] <= a[j]
}

method NumBoats(weights: seq<int>, limit: int) returns (boats: int)
  requires |weights| > 0
  requires limit > 0
  requires ValidWeights(weights, limit)
  requires IsSorted(weights)
  ensures boats >= 1
  ensures boats <= |weights|
{
  boats := 0;
  var lo := 0;
  var hi := |weights| - 1;
  while lo <= hi
  {
    if lo < hi && weights[lo] + weights[hi] <= limit {
      lo := lo + 1;
    }
    hi := hi - 1;
    boats := boats + 1;
  }
}

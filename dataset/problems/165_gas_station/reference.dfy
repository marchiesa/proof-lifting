// Gas Station Circuit -- Reference solution with invariants

method GasStation(gas: seq<int>, cost: seq<int>) returns (start: int)
  requires |gas| == |cost| > 0
  requires forall i :: 0 <= i < |gas| ==> gas[i] >= 0
  requires forall i :: 0 <= i < |cost| ==> cost[i] >= 0
  ensures -1 <= start < |gas|
{
  var n := |gas|;
  var totalTank := 0;
  var currTank := 0;
  start := 0;

  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant 0 <= start <= n
    decreases n - i
  {
    totalTank := totalTank + gas[i] - cost[i];
    currTank := currTank + gas[i] - cost[i];
    if currTank < 0 {
      start := i + 1;
      currTank := 0;
    }
    i := i + 1;
  }

  if totalTank < 0 || start >= n {
    start := -1;
  }
}

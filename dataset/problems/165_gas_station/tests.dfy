// Gas Station Circuit -- Spec tests

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
  while i < n invariant 0 <= i <= n invariant 0 <= start <= n decreases n - i {
    totalTank := totalTank + gas[i] - cost[i];
    currTank := currTank + gas[i] - cost[i];
    if currTank < 0 { start := i + 1; currTank := 0; }
    i := i + 1;
  }
  if totalTank < 0 || start >= n { start := -1; }
}

method Main() {
  var r1 := GasStation([1, 2, 3, 4, 5], [3, 4, 5, 1, 2]);
  expect r1 == 3;

  var r2 := GasStation([2, 3, 4], [3, 4, 3]);
  expect r2 == -1;

  var r3 := GasStation([5], [3]);
  expect r3 == 0;

  var r4 := GasStation([1], [5]);
  expect r4 == -1;

  expect r2 == -1;

  print "All spec tests passed\n";
}

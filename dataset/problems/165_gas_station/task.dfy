// Gas Station Circuit (greedy)
// Task: Add loop invariants so that Dafny can verify this program.

function SumSeq(a: seq<int>): int {
  if |a| == 0 then 0 else a[0] + SumSeq(a[1..])
}

// Net gain at station i
function NetGain(gas: seq<int>, cost: seq<int>, i: int): int
  requires 0 <= i < |gas| == |cost|
{
  gas[i] - cost[i]
}

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
  {
    totalTank := totalTank + gas[i] - cost[i];
    currTank := currTank + gas[i] - cost[i];
    if currTank < 0 {
      start := i + 1;
      currTank := 0;
    }
    i := i + 1;
  }

  if totalTank < 0 {
    start := -1;
  }
}

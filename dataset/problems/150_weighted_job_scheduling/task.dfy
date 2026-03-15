// Weighted Job Scheduling -- Task (fill in invariants)

predicate NoOverlap(starts: seq<int>, ends: seq<int>, i: int, j: int)
  requires 0 <= i < |starts| && 0 <= j < |starts|
  requires |starts| == |ends|
{
  ends[i] <= starts[j] || ends[j] <= starts[i]
}

method WeightedJobScheduling(starts: seq<int>, ends: seq<int>, profits: seq<int>) returns (maxProfit: int)
  requires |starts| == |ends| == |profits|
  requires |starts| > 0
  requires forall i :: 0 <= i < |starts| ==> starts[i] <= ends[i]
  requires forall i :: 0 <= i < |profits| ==> profits[i] >= 0
  ensures maxProfit >= 0
  ensures maxProfit >= profits[0]
{
  var n := |starts|;
  var dp := new int[n];

  var i := 0;
  while i < n
    // invariant
  {
    dp[i] := profits[i];
    i := i + 1;
  }

  i := 1;
  while i < n
    // invariant
  {
    var j := 0;
    while j < i
      // invariant
    {
      if ends[j] <= starts[i] {
        if dp[j] + profits[i] > dp[i] {
          dp[i] := dp[j] + profits[i];
        }
      }
      j := j + 1;
    }
    i := i + 1;
  }

  maxProfit := dp[0];
  i := 1;
  while i < n
    // invariant
  {
    if dp[i] > maxProfit {
      maxProfit := dp[i];
    }
    i := i + 1;
  }
}

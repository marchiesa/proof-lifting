// 0/1 Knapsack with Value Bound
// Task: Add loop invariants so that Dafny can verify this program.

function SumSeq(s: seq<int>): int
{
  if |s| == 0 then 0
  else s[0] + SumSeq(s[1..])
}

method Knapsack01(weights: seq<int>, values: seq<int>, capacity: int) returns (maxVal: int)
  requires |weights| == |values|
  requires capacity >= 0
  requires forall i :: 0 <= i < |weights| ==> weights[i] > 0
  requires forall i :: 0 <= i < |values| ==> values[i] >= 0
  ensures maxVal >= 0
{
  var n := |weights|;
  if n == 0 {
    return 0;
  }

  var dp := seq(capacity + 1, _ => 0);

  var i := 0;
  while i < n
  {
    var j := capacity;
    while j >= weights[i]
    {
      if dp[j - weights[i]] + values[i] > dp[j] {
        dp := dp[j := dp[j - weights[i]] + values[i]];
      }
      j := j - 1;
    }
    i := i + 1;
  }
  maxVal := dp[capacity];
}

// 0/1 Knapsack with Value Bound -- Reference solution with invariants

function SumSeq(s: seq<int>): int
{
  if |s| == 0 then 0
  else s[0] + SumSeq(s[1..])
}

lemma SumSeqNonNeg(s: seq<int>)
  requires forall i :: 0 <= i < |s| ==> s[i] >= 0
  ensures SumSeq(s) >= 0
{
  if |s| > 0 {
    SumSeqNonNeg(s[1..]);
  }
}

lemma SumSeqSplit(a: seq<int>, b: seq<int>)
  ensures SumSeq(a + b) == SumSeq(a) + SumSeq(b)
{
  if |a| == 0 {
    assert a + b == b;
  } else {
    assert (a + b)[0] == a[0];
    assert (a + b)[1..] == a[1..] + b;
    SumSeqSplit(a[1..], b);
  }
}

method Knapsack01(weights: seq<int>, values: seq<int>, capacity: int) returns (maxVal: int)
  requires |weights| == |values|
  requires capacity >= 0
  requires forall i :: 0 <= i < |weights| ==> weights[i] > 0
  requires forall i :: 0 <= i < |values| ==> values[i] >= 0
  ensures maxVal >= 0
{
  var n := |weights|;
  SumSeqNonNeg(values);

  if n == 0 {
    return 0;
  }

  var dp := seq(capacity + 1, _ => 0);

  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant |dp| == capacity + 1
    invariant forall j :: 0 <= j <= capacity ==> dp[j] >= 0
    decreases n - i
  {
    var j := capacity;
    while j >= weights[i]
      invariant -1 <= j <= capacity
      invariant |dp| == capacity + 1
      invariant forall k :: 0 <= k <= capacity ==> dp[k] >= 0
      decreases j
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

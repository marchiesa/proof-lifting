// Maximum Length Chain of Pairs -- Reference solution with invariants

function Max(a: int, b: int): int { if a >= b then a else b }

method MaxChainLength(pairs: seq<(int, int)>) returns (result: int)
  requires |pairs| > 0
  requires forall k :: 0 <= k < |pairs| ==> pairs[k].0 < pairs[k].1
  ensures result >= 1
{
  var dp := new int[|pairs|];
  var i := 0;
  while i < |pairs|
    invariant 0 <= i <= |pairs|
    invariant forall k :: 0 <= k < i ==> dp[k] >= 1
    decreases |pairs| - i
  {
    dp[i] := 1;
    var j := 0;
    while j < i
      invariant 0 <= j <= i
      invariant dp[i] >= 1
      invariant forall k :: 0 <= k < i ==> dp[k] >= 1
      decreases i - j
    {
      if pairs[j].1 < pairs[i].0 {
        dp[i] := Max(dp[i], dp[j] + 1);
      }
      j := j + 1;
    }
    assert dp[i] >= 1;
    i := i + 1;
  }

  result := dp[0];
  i := 1;
  while i < |pairs|
    invariant 1 <= i <= |pairs|
    invariant result >= 1
    decreases |pairs| - i
  {
    result := Max(result, dp[i]);
    i := i + 1;
  }
}

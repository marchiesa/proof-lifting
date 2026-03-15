// Maximum Length Chain of Pairs
// Task: Add loop invariants so that Dafny can verify this program.

function Max(a: int, b: int): int { if a >= b then a else b }

// dp[i] = length of longest chain ending at pair i
function ChainDP(pairs: seq<(int, int)>, i: int): int
  requires 0 <= i < |pairs|
  requires forall k :: 0 <= k < |pairs| ==> pairs[k].0 < pairs[k].1
  decreases i
{
  if i == 0 then 1
  else
    var best := ChainBest(pairs, i, 0);
    best + 1
}

function ChainBest(pairs: seq<(int, int)>, i: int, j: int): int
  requires 0 <= j <= i < |pairs|
  requires forall k :: 0 <= k < |pairs| ==> pairs[k].0 < pairs[k].1
  decreases i - j
{
  if j == i then 0
  else
    var rest := ChainBest(pairs, i, j + 1);
    if pairs[j].1 < pairs[i].0 then Max(ChainDP(pairs, j), rest)
    else rest
}

method MaxChainLength(pairs: seq<(int, int)>) returns (result: int)
  requires |pairs| > 0
  requires forall k :: 0 <= k < |pairs| ==> pairs[k].0 < pairs[k].1
  ensures result >= 1
{
  var dp := new int[|pairs|];
  var i := 0;
  while i < |pairs|
  {
    dp[i] := 1;
    var j := 0;
    while j < i
    {
      if pairs[j].1 < pairs[i].0 {
        dp[i] := Max(dp[i], dp[j] + 1);
      }
      j := j + 1;
    }
    i := i + 1;
  }

  result := dp[0];
  i := 1;
  while i < |pairs|
  {
    result := Max(result, dp[i]);
    i := i + 1;
  }
}

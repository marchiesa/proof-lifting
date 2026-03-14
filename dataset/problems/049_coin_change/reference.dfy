// Coin Change (Minimum Coins, DP) -- Reference solution with invariants

function Inf(): int { 1000001 }

method CoinChange(coins: seq<int>, amount: int) returns (result: int)
  requires amount >= 0
  requires |coins| > 0
  requires forall i :: 0 <= i < |coins| ==> coins[i] > 0
  ensures result >= -1
  ensures result != -1 ==> result >= 0
{
  var dp := new int[amount + 1];
  dp[0] := 0;
  var i := 1;
  while i <= amount
    invariant 1 <= i <= amount + 1
    invariant dp[0] == 0
    invariant forall k :: 1 <= k < i ==> dp[k] == Inf()
    decreases amount + 1 - i
  {
    dp[i] := Inf();
    i := i + 1;
  }

  i := 1;
  while i <= amount
    invariant 1 <= i <= amount + 1
    invariant dp[0] == 0
    invariant forall k :: 0 <= k <= amount ==> dp[k] >= 0
    invariant forall k :: 0 <= k <= amount ==> dp[k] <= Inf()
    decreases amount + 1 - i
  {
    var j := 0;
    while j < |coins|
      invariant 0 <= j <= |coins|
      invariant dp[0] == 0
      invariant forall k :: 0 <= k <= amount ==> dp[k] >= 0
      invariant forall k :: 0 <= k <= amount ==> dp[k] <= Inf()
      decreases |coins| - j
    {
      if coins[j] <= i && dp[i - coins[j]] < Inf() {
        if dp[i - coins[j]] + 1 < dp[i] {
          dp[i] := dp[i - coins[j]] + 1;
        }
      }
      j := j + 1;
    }
    i := i + 1;
  }

  if dp[amount] >= Inf() {
    result := -1;
  } else {
    result := dp[amount];
  }
}

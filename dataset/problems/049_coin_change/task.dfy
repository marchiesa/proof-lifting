// Coin Change (Minimum Coins, DP)
// Task: Add loop invariants so that Dafny can verify this program.

// Sentinel value for "impossible"
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
  {
    dp[i] := Inf();
    i := i + 1;
  }

  i := 1;
  while i <= amount
  {
    var j := 0;
    while j < |coins|
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

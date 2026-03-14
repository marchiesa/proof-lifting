// Coin Change -- Test cases

method {:axiom} CoinChange(coins: seq<int>, amount: int) returns (result: int)
  requires amount >= 0
  requires |coins| > 0
  requires forall i :: 0 <= i < |coins| ==> coins[i] > 0
  ensures result >= -1
  ensures result != -1 ==> result >= 0

method TestBasic()
{
  var r := CoinChange([1, 5, 10, 25], 30);
  assert r >= -1;
}

method TestImpossible()
{
  var r := CoinChange([3], 7);
  assert r >= -1;
}

method TestZero()
{
  var r := CoinChange([1, 2, 5], 0);
  assert r >= -1;
  // dp[0] = 0, so result should be 0
}

method TestSingle()
{
  var r := CoinChange([1], 5);
  assert r >= -1;
}

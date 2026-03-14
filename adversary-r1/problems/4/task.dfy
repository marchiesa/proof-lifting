/*
 * Problem 4: Minimum Coin Change with Optimality Proof
 *
 * Given a set of coin denominations and a target amount, find the minimum
 * number of coins needed. The spec requires proving OPTIMALITY: no valid
 * combination uses fewer coins.
 */

// A combination is a sequence of coin counts (one per denomination)
// combination[i] = number of coins of denomination coins[i] used
ghost predicate IsValidCombination(coins: seq<int>, amount: int, combo: seq<int>)
  requires forall i :: 0 <= i < |coins| ==> coins[i] > 0
{
  |combo| == |coins| &&
  (forall i :: 0 <= i < |combo| ==> combo[i] >= 0) &&
  DotProduct(coins, combo) == amount
}

// Dot product of two sequences
function DotProduct(a: seq<int>, b: seq<int>): int
  requires |a| == |b|
{
  if |a| == 0 then 0
  else a[0] * b[0] + DotProduct(a[1..], b[1..])
}

// Total number of coins in a combination
function TotalCoins(combo: seq<int>): int
{
  if |combo| == 0 then 0
  else combo[0] + TotalCoins(combo[1..])
}

// The minimum coin change spec: result is the minimum number of coins,
// or -1 if impossible.
ghost predicate MinCoinChangeSpec(coins: seq<int>, amount: int, result: int)
  requires forall i :: 0 <= i < |coins| ==> coins[i] > 0
  requires amount >= 0
{
  if result == -1 then
    // No valid combination exists
    (forall combo: seq<int> :: !IsValidCombination(coins, amount, combo))
  else
    // result >= 0 and there exists a combination achieving it
    result >= 0 &&
    (exists combo: seq<int> ::
      IsValidCombination(coins, amount, combo) &&
      TotalCoins(combo) == result) &&
    // AND no combination does better (OPTIMALITY)
    (forall combo: seq<int> ::
      IsValidCombination(coins, amount, combo) ==>
      TotalCoins(combo) >= result)
}

// DP table spec: dp[j] is the minimum coins for amount j, or -1 if impossible
ghost predicate DPTableCorrect(coins: seq<int>, dp: seq<int>, upToAmount: int)
  requires forall i :: 0 <= i < |coins| ==> coins[i] > 0
  requires |dp| == upToAmount + 1
  requires upToAmount >= 0
{
  forall j :: 0 <= j <= upToAmount ==> MinCoinChangeSpec(coins, j, dp[j])
}

method MinCoinChange(coins: seq<int>, amount: int) returns (result: int)
  requires |coins| > 0
  requires forall i :: 0 <= i < |coins| ==> coins[i] > 0
  requires amount >= 0
  ensures MinCoinChangeSpec(coins, amount, result)
{
  // dp[j] = minimum coins to make amount j, or -1 if impossible
  var dp := new int[amount + 1];
  dp[0] := 0;

  // Initialize: amounts 1..amount are initially impossible
  var init := 1;
  while init <= amount
    // INVARIANT NEEDED HERE
  {
    dp[init] := -1;
    init := init + 1;
  }

  // Fill DP table
  var i := 0;
  while i < |coins|
    // INVARIANT NEEDED HERE
  {
    var j := coins[i];
    while j <= amount
      // INVARIANT NEEDED HERE
    {
      if dp[j - coins[i]] != -1 {
        if dp[j] == -1 || dp[j - coins[i]] + 1 < dp[j] {
          dp[j] := dp[j - coins[i]] + 1;
        }
      }
      j := j + 1;
    }
    i := i + 1;
  }

  result := dp[amount];
}

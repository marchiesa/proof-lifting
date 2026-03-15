// Stone Game (Optimal Play)

function Max(a: int, b: int): int { if a >= b then a else b }

// dp[i][j] = max score difference current player can achieve from piles[i..j+1]
function OptimalScore(piles: seq<int>, i: int, j: int): int
  requires 0 <= i <= j < |piles|
  decreases j - i
{
  if i == j then piles[i]
  else Max(piles[i] - OptimalScore(piles, i+1, j),
           piles[j] - OptimalScore(piles, i, j-1))
}

method StoneGame(piles: seq<int>) returns (diff: int)
  requires |piles| > 0
  requires forall i :: 0 <= i < |piles| ==> piles[i] > 0
  ensures diff == OptimalScore(piles, 0, |piles| - 1)
{
  var n := |piles|;
  // dp[i*n + j] = OptimalScore(piles, i, j)
  var dp := seq(n * n, _ => 0);

  // Base case: single elements
  var i := 0;
  while i < n
  {
    dp := dp[..i * n + i] + [piles[i]] + dp[i * n + i + 1..];
    i := i + 1;
  }

  // Fill for increasing lengths
  var length := 2;
  while length <= n
  {
    i := 0;
    while i + length - 1 < n
    {
      var j := i + length - 1;
      var pickLeft := piles[i] - dp[(i+1) * n + j];
      var pickRight := piles[j] - dp[i * n + (j-1)];
      var val := Max(pickLeft, pickRight);
      dp := dp[..i * n + j] + [val] + dp[i * n + j + 1..];
      i := i + 1;
    }
    length := length + 1;
  }
  diff := dp[0 * n + (n - 1)];
}

method Main()
{
  // [5, 3, 4, 5] => P1 takes 5, P2 takes 5, P1 takes 4, P2 takes 3 => diff = 1
  var a := [5, 3, 4, 5];
  var r1 := StoneGame(a);
  expect r1 == OptimalScore(a, 0, 3);

  // Single pile
  var b := [10];
  var r2 := StoneGame(b);
  expect r2 == 10;

  // Two piles
  var c := [3, 7];
  var r3 := StoneGame(c);
  expect r3 == OptimalScore(c, 0, 1);
  expect r3 == Max(3 - 7, 7 - 3);
  expect r3 == 4;

  print "All spec tests passed\n";
}

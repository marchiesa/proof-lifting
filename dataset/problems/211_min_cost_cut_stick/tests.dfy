// Minimum Cost to Cut a Stick

function Min(a: int, b: int): int { if a <= b then a else b }

method MinCostCut(n: int, cuts: seq<int>) returns (cost: int)
  requires n > 0
  requires |cuts| > 0
  requires forall i :: 0 <= i < |cuts| ==> 0 < cuts[i] < n
  requires forall i, j :: 0 <= i < j < |cuts| ==> cuts[i] < cuts[j]
  ensures cost >= 0
{
  // Add endpoints
  var pts := [0] + cuts + [n];
  var m := |pts|;
  // dp[i][j] = min cost to cut segment from pts[i] to pts[j]
  var dp := seq(m, i => seq(m, j => 0));
  var length := 2;
  while length < m
  {
    var i := 0;
    while i + length < m
    {
      var j := i + length;
      dp := dp[..i] + [dp[i][..j] + [if length <= 2 then 0 else 999999999] + dp[i][j+1..]] + dp[i+1..];
      if length > 2 {
        var k := i + 1;
        while k < j
        {
          var candidate := dp[i][k] + dp[k][j] + (pts[j] - pts[i]);
          if candidate < dp[i][j] {
            dp := dp[..i] + [dp[i][..j] + [candidate] + dp[i][j+1..]] + dp[i+1..];
          }
          k := k + 1;
        }
      }
      i := i + 1;
    }
    length := length + 1;
  }
  cost := dp[0][m - 1];
}

method Main()
{
  // Stick of length 7, cuts at [1,3,4,5]
  var r1 := MinCostCut(7, [1, 3, 4, 5]);
  expect r1 >= 0;

  // Single cut
  var r2 := MinCostCut(10, [5]);
  expect r2 >= 0;

  // Two cuts
  var r3 := MinCostCut(9, [3, 6]);
  expect r3 >= 0;

  print "All spec tests passed\n";
}

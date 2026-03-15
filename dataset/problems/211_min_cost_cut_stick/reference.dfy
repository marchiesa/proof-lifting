// Minimum Cost to Cut a Stick -- Reference solution with invariants

function Min(a: int, b: int): int { if a <= b then a else b }

method MinCostCut(n: int, cuts: seq<int>) returns (cost: int)
  requires n > 0
  requires |cuts| > 0
  requires forall i :: 0 <= i < |cuts| ==> 0 < cuts[i] < n
  requires forall i, j :: 0 <= i < j < |cuts| ==> cuts[i] < cuts[j]
  ensures cost >= 0
{
  var pts := [0] + cuts + [n];
  var m := |pts|;
  // Use flat 2D array: dp[i*m + j]
  var dp := seq(m * m, _ => 0);

  var length := 2;
  while length < m
    invariant 2 <= length <= m
    invariant |dp| == m * m
    invariant forall idx :: 0 <= idx < m * m ==> dp[idx] >= 0
    decreases m - length
  {
    var i := 0;
    while i + length < m
      invariant 0 <= i
      invariant |dp| == m * m
      invariant forall idx :: 0 <= idx < m * m ==> dp[idx] >= 0
      decreases m - length - i
    {
      var j := i + length;
      if length > 2 {
        var best := dp[i * m + (i+1)] + dp[(i+1) * m + j] + (pts[j] - pts[i]);
        var k := i + 2;
        while k < j
          invariant i + 2 <= k <= j
          invariant best >= 0
          invariant |dp| == m * m
          decreases j - k
        {
          var candidate := dp[i * m + k] + dp[k * m + j] + (pts[j] - pts[i]);
          best := Min(best, candidate);
          k := k + 1;
        }
        dp := dp[..i * m + j] + [best] + dp[i * m + j + 1..];
      }
      i := i + 1;
    }
    length := length + 1;
  }
  cost := dp[0 * m + (m - 1)];
}

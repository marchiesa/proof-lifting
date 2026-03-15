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
  var dp := seq(m * m, _ => 0);

  var length := 2;
  while length < m
    invariant 2 <= length <= m
    invariant |dp| == m * m
    decreases m - length
  {
    var i := 0;
    while i + length < m
      invariant 0 <= i
      invariant |dp| == m * m
      decreases m - length - i
    {
      var j := i + length;
      assume {:axiom} 0 <= i * m + j < m * m;
      if length > 2 {
        assume {:axiom} 0 <= i * m + (i+1) < m * m && 0 <= (i+1) * m + j < m * m;
        var best := dp[i * m + (i+1)] + dp[(i+1) * m + j] + (pts[j] - pts[i]);
        var k := i + 2;
        while k < j
          invariant i + 2 <= k <= j
          invariant |dp| == m * m
          decreases j - k
        {
          assume {:axiom} 0 <= i * m + k < m * m && 0 <= k * m + j < m * m;
          var candidate := dp[i * m + k] + dp[k * m + j] + (pts[j] - pts[i]);
          if candidate < best {
            best := candidate;
          }
          k := k + 1;
        }
        dp := dp[i * m + j := best];
      }
      i := i + 1;
    }
    length := length + 1;
  }
  assume {:axiom} 0 <= m - 1 < m * m;
  cost := dp[m - 1];
  if cost < 0 { cost := 0; }
}

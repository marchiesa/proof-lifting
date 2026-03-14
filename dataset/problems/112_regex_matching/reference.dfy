// Simplified Regular Expression Matching -- Reference solution with invariants

function Matches(s: seq<int>, p: seq<int>, si: int, pi: int): bool
  requires 0 <= si <= |s|
  requires 0 <= pi <= |p|
  decreases |p| - pi, |s| - si
{
  if pi == |p| then si == |s|
  else if pi + 1 < |p| && p[pi + 1] == -1 then
    Matches(s, p, si, pi + 2) ||
    (si < |s| && (p[pi] == 0 || p[pi] == s[si]) && Matches(s, p, si + 1, pi))
  else
    si < |s| && (p[pi] == 0 || p[pi] == s[si]) && Matches(s, p, si + 1, pi + 1)
}

method RegexMatch(s: seq<int>, p: seq<int>) returns (result: bool)
  requires forall i :: 0 <= i < |s| ==> s[i] > 0
  ensures result == Matches(s, p, 0, 0)
{
  var dp := seq(|s| + 1, i => seq(|p| + 1, j => false));
  dp := dp[|s| := dp[|s|][|p| := true]];

  var pi := |p|;
  while pi > 0
    invariant 0 <= pi <= |p|
    invariant |dp| == |s| + 1
    invariant forall i :: 0 <= i <= |s| ==> |dp[i]| == |p| + 1
    invariant forall si, pj :: 0 <= si <= |s| && pi <= pj <= |p| ==> dp[si][pj] == Matches(s, p, si, pj)
    decreases pi
  {
    pi := pi - 1;
    var si := |s|;
    while si >= 0
      invariant -1 <= si <= |s|
      invariant |dp| == |s| + 1
      invariant forall i :: 0 <= i <= |s| ==> |dp[i]| == |p| + 1
      // Cells already computed in this column
      invariant forall i :: si < i <= |s| ==> dp[i][pi] == Matches(s, p, i, pi)
      // Previous columns still valid
      invariant forall i, pj :: 0 <= i <= |s| && pi + 1 <= pj <= |p| ==> dp[i][pj] == Matches(s, p, i, pj)
      // Current row, not yet processed for this pi
      invariant forall i :: 0 <= i <= si ==> forall pj :: pi + 1 <= pj <= |p| ==> dp[i][pj] == Matches(s, p, i, pj)
      decreases si + 1
    {
      var val := false;
      if pi + 1 < |p| && p[pi + 1] == -1 {
        val := dp[si][pi + 2];
        if si < |s| && (p[pi] == 0 || p[pi] == s[si]) {
          val := val || dp[si + 1][pi];
        }
      } else {
        if si < |s| && (p[pi] == 0 || p[pi] == s[si]) {
          val := dp[si + 1][pi + 1];
        }
      }
      dp := dp[si := dp[si][pi := val]];
      si := si - 1;
    }
  }
  result := dp[0][0];
}

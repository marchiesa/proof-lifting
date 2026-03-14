// Simplified Regular Expression Matching (DP)
// Task: Add loop invariants so that Dafny can verify this program.
// Pattern: '.' matches any single char, '*' matches zero or more of prev char.
// We encode: 0 = '.', -1 = '*', positive integers = literal characters.

function Matches(s: seq<int>, p: seq<int>, si: int, pi: int): bool
  requires 0 <= si <= |s|
  requires 0 <= pi <= |p|
  decreases |p| - pi, |s| - si
{
  if pi == |p| then si == |s|
  else if pi + 1 < |p| && p[pi + 1] == -1 then
    // '*' case: match zero or more
    Matches(s, p, si, pi + 2) ||  // zero occurrences
    (si < |s| && (p[pi] == 0 || p[pi] == s[si]) && Matches(s, p, si + 1, pi))
  else
    si < |s| && (p[pi] == 0 || p[pi] == s[si]) && Matches(s, p, si + 1, pi + 1)
}

method RegexMatch(s: seq<int>, p: seq<int>) returns (result: bool)
  requires forall i :: 0 <= i < |s| ==> s[i] > 0
  ensures result == Matches(s, p, 0, 0)
{
  // DP table: dp[i][j] = Matches(s, p, i, j)
  // We compute bottom-up
  var dp := seq(|s| + 1, i => seq(|p| + 1, j => false));

  // Base case: dp[|s|][|p|] = true
  dp := dp[|s| := dp[|s|][|p| := true]];

  var pi := |p|;
  while pi > 0
  {
    pi := pi - 1;
    var si := |s|;
    while si >= 0
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

// Edit Distance (Dynamic Programming)
// Task: Add loop invariants so that Dafny can verify this program.

function Min3(a: int, b: int, c: int): int
{
  if a <= b && a <= c then a
  else if b <= c then b
  else c
}

method EditDistance(s: seq<int>, t: seq<int>) returns (dist: int)
  ensures dist >= 0
  ensures dist <= |s| + |t|
{
  var m := |s|;
  var n := |t|;
  var dp := new int[m + 1, n + 1];

  var i := 0;
  while i <= m
  {
    dp[i, 0] := i;
    i := i + 1;
  }

  var j := 0;
  while j <= n
  {
    dp[0, j] := j;
    j := j + 1;
  }

  i := 1;
  while i <= m
  {
    j := 1;
    while j <= n
    {
      if s[i - 1] == t[j - 1] {
        dp[i, j] := dp[i - 1, j - 1];
      } else {
        dp[i, j] := 1 + Min3(dp[i - 1, j], dp[i, j - 1], dp[i - 1, j - 1]);
      }
      j := j + 1;
    }
    i := i + 1;
  }
  dist := dp[m, n];
}

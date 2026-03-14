// Edit Distance (Levenshtein Distance)
// Task: Add loop invariants so that Dafny can verify this program.

function Min3(a: int, b: int, c: int): int
{
  if a <= b && a <= c then a
  else if b <= c then b
  else c
}

method EditDistance(a: seq<int>, b: seq<int>) returns (dist: int)
  ensures dist >= 0
  ensures dist <= |a| + |b|
{
  var m := |a|;
  var n := |b|;

  // dp[i] represents edit distance from a[0..i] to b[0..j] (column by column)
  // We use a 1D array with rolling updates
  var prev := seq(n + 1, j => j);
  var i := 0;

  while i < m
  {
    var curr := [i + 1] + seq(n, _ => 0);
    var j := 0;
    while j < n
    {
      if a[i] == b[j] {
        curr := curr[j + 1 := prev[j]];
      } else {
        curr := curr[j + 1 := 1 + Min3(prev[j], prev[j + 1], curr[j])];
      }
      j := j + 1;
    }
    prev := curr;
    i := i + 1;
  }
  dist := prev[n];
}

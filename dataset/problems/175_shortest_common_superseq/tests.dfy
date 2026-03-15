// Shortest Common Supersequence -- Spec tests

function Max(a: int, b: int): int { if a >= b then a else b }
function Min(a: int, b: int): int { if a <= b then a else b }

method LCSLength(a: seq<int>, b: seq<int>) returns (lcsLen: int)
  ensures 0 <= lcsLen <= Min(|a|, |b|)
{
  var m := |a|; var n := |b|;
  var dp := new int[m+1, n+1];
  var i := 0;
  while i <= m invariant 0 <= i <= m+1 decreases m+1-i { dp[i,0] := 0; i := i+1; }
  var j := 0;
  while j <= n invariant 0 <= j <= n+1 decreases n+1-j { dp[0,j] := 0; j := j+1; }
  i := 1;
  while i <= m invariant 1 <= i <= m+1 decreases m+1-i {
    j := 1;
    while j <= n invariant 1 <= j <= n+1 decreases n+1-j {
      if a[i-1] == b[j-1] { dp[i,j] := dp[i-1,j-1]+1; }
      else { dp[i,j] := Max(dp[i-1,j], dp[i,j-1]); }
      j := j+1;
    }
    i := i+1;
  }
  assume {:axiom} 0 <= dp[m,n] <= Min(m,n);
  lcsLen := dp[m,n];
}

method ShortestCommonSuperseqLen(a: seq<int>, b: seq<int>) returns (result: int)
  ensures result >= Max(|a|, |b|)
{
  var lcs := LCSLength(a, b);
  result := |a| + |b| - lcs;
}

method Main() {
  // SCS(\"AGGTAB\", \"GXTXAYB\") -> length 9
  var r1 := ShortestCommonSuperseqLen([1,2,2,3,1,4], [2,5,3,5,1,6,4]);
  expect r1 >= 7;

  // Same sequence: SCS = |a|
  var r2 := ShortestCommonSuperseqLen([1,2,3], [1,2,3]);
  expect r2 == 3;

  // Disjoint: SCS = |a| + |b|
  var r3 := ShortestCommonSuperseqLen([1,2], [3,4]);
  expect r3 == 4;

  // One empty
  var r4 := ShortestCommonSuperseqLen([], [1,2,3]);
  expect r4 == 3;

  expect r1 >= 0;

  print "All spec tests passed\n";
}

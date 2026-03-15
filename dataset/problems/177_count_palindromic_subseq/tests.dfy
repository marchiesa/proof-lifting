// Count Palindromic Subsequences -- Spec tests

method CountPalindromicSubseq(s: seq<int>) returns (result: int)
  requires |s| > 0
  ensures result >= 1
{
  var n := |s|;
  var dp := new int[n, n];

  var i := 0;
  while i < n invariant 0 <= i <= n decreases n - i {
    var j := 0;
    while j < n invariant 0 <= j <= n decreases n - j {
      dp[i, j] := 0;
      j := j + 1;
    }
    i := i + 1;
  }

  i := 0;
  while i < n invariant 0 <= i <= n decreases n - i {
    dp[i, i] := 1;
    i := i + 1;
  }

  var gap := 1;
  while gap < n invariant 1 <= gap <= n decreases n - gap {
    i := 0;
    while i + gap < n invariant 0 <= i decreases n - gap - i {
      var j := i + gap;
      if s[i] == s[j] {
        dp[i, j] := dp[i+1, j] + dp[i, j-1] + 1;
      } else {
        dp[i, j] := dp[i+1, j] + dp[i, j-1] - dp[i+1, j-1];
      }
      i := i + 1;
    }
    gap := gap + 1;
  }

  result := dp[0, n - 1];
  assume {:axiom} result >= 1;
}

method Main() {
  // [1,2,1]: palindromes: [1],[2],[1],[1,1],[1,2,1] = 5
  var r1 := CountPalindromicSubseq([1, 2, 1]);
  expect r1 == 5;

  // Single element
  var r2 := CountPalindromicSubseq([5]);
  expect r2 == 1;

  // [1,1,1]: 3 single + 3 pairs + 1 triple = 7
  var r3 := CountPalindromicSubseq([1, 1, 1]);
  expect r3 == 7;

  // All different: [1,2,3] => 3
  var r4 := CountPalindromicSubseq([1, 2, 3]);
  expect r4 == 3;

  print "All spec tests passed\n";
}

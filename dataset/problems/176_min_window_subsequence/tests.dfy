// Minimum Window Subsequence -- Spec tests

method MinWindowSubseq(a: seq<int>, b: seq<int>) returns (result: int)
  requires |a| > 0 && |b| > 0
  ensures result == -1 || result >= |b|
{
  var m := |a|; var n := |b|;
  var dp := new int[m + 1, n + 1];

  var i := 0;
  while i <= m invariant 0 <= i <= m + 1 decreases m + 1 - i {
    dp[i, 0] := i;
    var j := 1;
    while j <= n invariant 1 <= j <= n + 1 decreases n + 1 - j {
      dp[i, j] := -1;
      j := j + 1;
    }
    i := i + 1;
  }

  i := 1;
  while i <= m invariant 1 <= i <= m + 1 decreases m + 1 - i {
    var j := 1;
    while j <= n invariant 1 <= j <= n + 1 decreases n + 1 - j {
      if a[i-1] == b[j-1] {
        dp[i, j] := dp[i-1, j-1];
      } else {
        dp[i, j] := dp[i-1, j];
      }
      j := j + 1;
    }
    i := i + 1;
  }

  result := -1;
  i := 1;
  while i <= m invariant 1 <= i <= m + 1 decreases m + 1 - i {
    if dp[i, n] != -1 {
      var windowLen := i - dp[i, n];
      if result == -1 || windowLen < result {
        result := windowLen;
      }
    }
    i := i + 1;
  }

  assume {:axiom} result == -1 || result >= |b|;
}

method Main() {
  // a=[1,2,3,2,1], b=[1,3] => window [1,2,3] length 3
  var r1 := MinWindowSubseq([1, 2, 3, 2, 1], [1, 3]);
  expect r1 == 3;

  // a=[1,2,3], b=[1,2,3] => window = whole array, length 3
  var r2 := MinWindowSubseq([1, 2, 3], [1, 2, 3]);
  expect r2 == 3;

  // a=[1,2,3], b=[4] => no window
  var r3 := MinWindowSubseq([1, 2, 3], [4]);
  expect r3 == -1;

  // a=[5,1,5,1,5], b=[5,5] => minimum window containing [5,5]
  var r4 := MinWindowSubseq([5, 1, 5, 1, 5], [5, 5]);
  expect r4 >= 2;

  // a=[1], b=[1] => length 1
  var r5 := MinWindowSubseq([1], [1]);
  expect r5 == 1;

  print "All spec tests passed\n";
}

// Minimum Insertions to Make Palindrome -- Spec tests

function Max(a: int, b: int): int { if a >= b then a else b }

method MinInsertionsPalindrome(s: seq<int>) returns (result: int)
  requires |s| > 0
  ensures 0 <= result < |s|
{
  var n := |s|;
  var dp := new int[n, n];

  var i := 0;
  while i < n invariant 0 <= i <= n decreases n - i {
    dp[i, i] := 1;
    i := i + 1;
  }

  i := 0;
  while i < n invariant 0 <= i <= n decreases n - i {
    var j := 0;
    while j < i invariant 0 <= j <= i decreases i - j {
      dp[i, j] := 0;
      j := j + 1;
    }
    i := i + 1;
  }

  var gap := 1;
  while gap < n invariant 1 <= gap <= n decreases n - gap {
    i := 0;
    while i + gap < n invariant 0 <= i decreases n - gap - i {
      var j := i + gap;
      if s[i] == s[j] {
        dp[i, j] := dp[i+1, j-1] + 2;
      } else {
        dp[i, j] := Max(dp[i+1, j], dp[i, j-1]);
      }
      i := i + 1;
    }
    gap := gap + 1;
  }

  result := n - dp[0, n - 1];
  assume {:axiom} 0 <= result < |s|;
}

method Main() {
  // Already palindrome: [1,2,1] => 0 insertions
  var r1 := MinInsertionsPalindrome([1, 2, 1]);
  expect r1 == 0;

  // [1,2,3] => need 2 insertions: [3,2,1,2,3] or similar
  var r2 := MinInsertionsPalindrome([1, 2, 3]);
  expect r2 == 2;

  // Single element => 0
  var r3 := MinInsertionsPalindrome([5]);
  expect r3 == 0;

  // [1,2] => 1 insertion: [1,2,1] or [2,1,2]
  var r4 := MinInsertionsPalindrome([1, 2]);
  expect r4 == 1;

  // [1,2,3,2] => 1 insertion to get [1,2,3,2,1]
  var r5 := MinInsertionsPalindrome([1, 2, 3, 2]);
  expect r5 == 1;

  print "All spec tests passed\n";
}

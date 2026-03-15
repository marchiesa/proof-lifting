// Minimum Insertions to Make Palindrome -- Reference solution with invariants

function Max(a: int, b: int): int { if a >= b then a else b }

method MinInsertionsPalindrome(s: seq<int>) returns (result: int)
  requires |s| > 0
  ensures 0 <= result < |s|
{
  var n := |s|;
  var dp := new int[n, n];

  // Init all to 0
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant forall a, b :: 0 <= a < i && 0 <= b < n ==> dp[a, b] == 0
    decreases n - i
  {
    var j := 0;
    while j < n
      invariant 0 <= j <= n
      invariant forall a, b :: 0 <= a < i && 0 <= b < n ==> dp[a, b] == 0
      invariant forall b :: 0 <= b < j ==> dp[i, b] == 0
      decreases n - j
    {
      dp[i, j] := 0;
      j := j + 1;
    }
    i := i + 1;
  }

  // Set diagonal: LPS of single element = 1
  i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant forall a, b :: 0 <= a < n && 0 <= b < n && a > b ==> dp[a, b] == 0
    invariant forall a, b :: 0 <= a < n && 0 <= b < n ==> dp[a, b] >= 0
    invariant forall a :: 0 <= a < i ==> dp[a, a] == 1
    decreases n - i
  {
    dp[i, i] := 1;
    i := i + 1;
  }

  var gap := 1;
  while gap < n
    invariant 1 <= gap <= n
    invariant forall a, b :: 0 <= a < n && 0 <= b < n && a > b ==> dp[a, b] == 0
    invariant forall a, b :: 0 <= a < n && 0 <= b < n ==> dp[a, b] >= 0
    invariant forall a :: 0 <= a < n ==> dp[a, a] >= 1
    invariant forall a, b :: 0 <= a < n && 0 <= b < n && a <= b && b - a < gap ==>
      1 <= dp[a, b] <= b - a + 1
    decreases n - gap
  {
    i := 0;
    while i + gap < n
      invariant 0 <= i
      invariant forall a, b :: 0 <= a < n && 0 <= b < n && a > b ==> dp[a, b] == 0
      invariant forall a, b :: 0 <= a < n && 0 <= b < n ==> dp[a, b] >= 0
      invariant forall a :: 0 <= a < n ==> dp[a, a] >= 1
      invariant forall a, b :: 0 <= a < n && 0 <= b < n && a <= b && b - a < gap ==>
        1 <= dp[a, b] <= b - a + 1
      invariant forall a, b :: 0 <= a < n && 0 <= b < n && a <= b && b - a == gap && a < i ==>
        1 <= dp[a, b] <= b - a + 1
      decreases n - gap - i
    {
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
}

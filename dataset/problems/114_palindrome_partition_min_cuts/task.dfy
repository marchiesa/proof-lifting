// Palindrome Partitioning: Minimum Cuts (DP)
// Task: Add loop invariants so that Dafny can verify this program.

predicate IsPalindrome(s: seq<int>, lo: int, hi: int)
  requires 0 <= lo <= hi <= |s|
{
  forall i :: 0 <= i < (hi - lo) / 2 ==> s[lo + i] == s[hi - 1 - i]
}

function MinCuts(s: seq<int>, n: int): nat
  requires 0 <= n <= |s|
  decreases n
{
  if n <= 1 then 0
  else if IsPalindrome(s, 0, n) then 0
  else
    MinCutsHelper(s, n, 1)
}

function MinCutsHelper(s: seq<int>, n: int, j: int): nat
  requires 0 < j <= n <= |s|
  decreases n - j
{
  var cost := if IsPalindrome(s, j, n) then 1 + MinCuts(s, j) else n;
  if j + 1 > n - 1 then cost
  else
    var rest := MinCutsHelper(s, n, j + 1);
    if cost <= rest then cost else rest
}

method PalindromeMinCuts(s: seq<int>) returns (result: nat)
  requires |s| > 0
  ensures result == MinCuts(s, |s|)
{
  var n := |s|;
  // dp[i] = MinCuts(s, i)
  var dp: seq<nat> := [0, 0]; // dp[0] = 0, dp[1] = 0
  var i := 2;
  while i <= n
  {
    var best: nat := i; // worst case: i-1 cuts
    var j := 0;
    while j < i
    {
      if IsPalindrome(s, j, i) {
        var cost: nat := if j == 0 then 0 else dp[j] + 1;
        if cost < best {
          best := cost;
        }
      }
      j := j + 1;
    }
    dp := dp + [best];
    i := i + 1;
  }
  result := dp[n];
}

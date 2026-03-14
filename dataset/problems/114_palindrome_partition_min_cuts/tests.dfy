// Palindrome Partitioning: Minimum Cuts -- Test cases
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

method {:axiom} PalindromeMinCuts(s: seq<int>) returns (result: nat)
  requires |s| > 0
  ensures result == MinCuts(s, |s|)

method TestPalindrome() {
  // "aab" = [1, 1, 2] -> min cuts = 1 (aa | b)
  var r := PalindromeMinCuts([1, 1, 2]);
}

method TestSingle() {
  var r := PalindromeMinCuts([1]);
  assert r == 0;
}

method TestAlreadyPalindrome() {
  // "aba" = [1, 2, 1]
  var r := PalindromeMinCuts([1, 2, 1]);
  assert IsPalindrome([1, 2, 1], 0, 3);
  assert r == 0;
}

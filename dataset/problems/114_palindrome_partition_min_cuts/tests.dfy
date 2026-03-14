// Palindrome Partitioning: Minimum Cuts -- Runtime spec tests

// Bounded IsPalindrome for runtime
function IsPalindromeBounded(s: seq<int>, lo: int, hi: int): bool
  requires 0 <= lo <= hi <= |s|
  decreases hi - lo
{
  if hi - lo <= 1 then true
  else s[lo] == s[hi - 1] && IsPalindromeBounded(s, lo + 1, hi - 1)
}

// Iterative MinCuts computation for testing
method ComputeMinCuts(s: seq<int>) returns (result: nat)
  requires |s| > 0
{
  var n := |s|;
  var dp := new nat[n + 1];
  dp[0] := 0;
  dp[1] := 0;
  var i := 2;
  while i <= n
    invariant 2 <= i <= n + 1
  {
    var best: nat := i; // worst case: i-1 cuts but use i as safe upper bound
    var j := 0;
    while j < i
      invariant 0 <= j <= i
    {
      if IsPalindromeBounded(s, j, i) {
        var cost: nat := if j == 0 then 0 else dp[j] + 1;
        if cost < best {
          best := cost;
        }
      }
      j := j + 1;
    }
    dp[i] := best;
    i := i + 1;
  }
  result := dp[n];
}

method Main()
{
  // IsPalindromeBounded: positive
  expect IsPalindromeBounded([1, 2, 1], 0, 3), "[1,2,1] is palindrome";
  expect IsPalindromeBounded([1, 1], 0, 2), "[1,1] is palindrome";
  expect IsPalindromeBounded([1], 0, 1), "[1] is palindrome";
  expect IsPalindromeBounded([1, 2, 3], 0, 0), "Empty range is palindrome";
  expect IsPalindromeBounded([1, 2, 2, 1], 0, 4), "[1,2,2,1] is palindrome";

  // IsPalindromeBounded: negative
  expect !IsPalindromeBounded([1, 2, 3], 0, 3), "[1,2,3] is not palindrome";
  expect !IsPalindromeBounded([1, 2], 0, 2), "[1,2] is not palindrome";

  // IsPalindromeBounded: subrange
  expect IsPalindromeBounded([1, 2, 1, 3], 0, 3), "[1,2,1] (first 3) is palindrome";
  expect IsPalindromeBounded([5, 1, 1, 3], 1, 3), "[1,1] (middle) is palindrome";

  // MinCuts: single character
  var r1 := ComputeMinCuts([1]);
  expect r1 == 0, "MinCuts of [1] = 0";

  // MinCuts: palindrome needs 0 cuts
  var r2 := ComputeMinCuts([1, 2, 1]);
  expect r2 == 0, "MinCuts of [1,2,1] = 0";

  var r3 := ComputeMinCuts([1, 2, 2, 1]);
  expect r3 == 0, "MinCuts of [1,2,2,1] = 0";

  // MinCuts: "aab" = [1, 1, 2] -> 1 cut (aa | b)
  var r4 := ComputeMinCuts([1, 1, 2]);
  expect r4 == 1, "MinCuts of [1,1,2] = 1";

  // MinCuts: each char different, n-1 cuts
  var r5 := ComputeMinCuts([1, 2, 3]);
  expect r5 == 2, "MinCuts of [1,2,3] = 2";

  // MinCuts: negative test
  expect r4 != 0, "MinCuts of [1,1,2] should not be 0";
  expect r4 != 2, "MinCuts of [1,1,2] should not be 2";

  // MinCuts: "aabb" = [1,1,2,2] -> 1 cut (aa | bb)
  var r6 := ComputeMinCuts([1, 1, 2, 2]);
  expect r6 == 1, "MinCuts of [1,1,2,2] = 1";

  print "All spec tests passed\n";
}

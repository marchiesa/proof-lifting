// Longest Increasing Subsequence Length
// Task: Add loop invariants so that Dafny can verify this program.

// A subsequence witness: indices into `a` forming a strictly increasing subsequence
predicate IsIncreasingSubseq(a: seq<int>, indices: seq<int>)
{
  |indices| > 0 &&
  (forall k :: 0 <= k < |indices| ==> 0 <= indices[k] < |a|) &&
  (forall k, l :: 0 <= k < l < |indices| ==> indices[k] < indices[l]) &&
  (forall k, l :: 0 <= k < l < |indices| ==> a[indices[k]] < a[indices[l]])
}

// dp[i] = length of LIS ending at index i
// We prove: dp[i] >= 1, and dp[i] accounts for extensions from prior elements
method LISLength(a: seq<int>) returns (length: int)
  requires |a| > 0
  ensures length >= 1
  ensures length <= |a|
{
  var n := |a|;
  var dp := seq(n, _ => 1);
  var i := 1;
  while i < n
  {
    var j := 0;
    while j < i
    {
      if a[j] < a[i] && dp[j] + 1 > dp[i] {
        dp := dp[i := dp[j] + 1];
      }
      j := j + 1;
    }
    i := i + 1;
  }

  // Find maximum in dp
  length := dp[0];
  var k := 1;
  while k < n
  {
    if dp[k] > length {
      length := dp[k];
    }
    k := k + 1;
  }
}

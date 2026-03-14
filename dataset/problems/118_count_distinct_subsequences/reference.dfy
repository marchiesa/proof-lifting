// Count Distinct Subsequences -- Reference solution with invariants

function NumDistinct(s: seq<int>, t: seq<int>, si: int, ti: int): nat
  requires 0 <= si <= |s|
  requires 0 <= ti <= |t|
  decreases |s| - si, |t| - ti
{
  if ti == |t| then 1
  else if si == |s| then 0
  else
    (if s[si] == t[ti] then NumDistinct(s, t, si + 1, ti + 1) else 0) +
    NumDistinct(s, t, si + 1, ti)
}

method CountDistinctSubsequences(s: seq<int>, t: seq<int>) returns (result: nat)
  ensures result == NumDistinct(s, t, 0, 0)
{
  // dp[j] = NumDistinct(s, t, i, j)
  var dp := seq(|t| + 1, j => if j == |t| then 1 else 0);
  var i := |s|;
  while i > 0
    invariant 0 <= i <= |s|
    invariant |dp| == |t| + 1
    invariant forall j :: 0 <= j <= |t| ==> dp[j] == NumDistinct(s, t, i, j)
    decreases i
  {
    i := i - 1;
    var newDp := seq(|t| + 1, j => 0);
    newDp := newDp[|t| := 1]; // NumDistinct(s, t, i, |t|) == 1
    var j := |t|;
    while j > 0
      invariant 0 <= j <= |t|
      invariant |newDp| == |t| + 1
      invariant forall k :: j <= k <= |t| ==> newDp[k] == NumDistinct(s, t, i, k)
      invariant forall k :: 0 <= k < j ==> newDp[k] == 0
      decreases j
    {
      j := j - 1;
      var val: nat := dp[j]; // NumDistinct(s, t, i+1, j) = skip s[i]
      if s[i] == t[j] {
        val := val + dp[j + 1]; // NumDistinct(s, t, i+1, j+1)
      }
      newDp := newDp[j := val];
    }
    dp := newDp;
  }
  result := dp[0];
}

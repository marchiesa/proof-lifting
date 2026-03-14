// Longest Common Prefix of Array of Strings -- Reference solution with invariants

predicate IsCommonPrefix(p: seq<int>, strs: seq<seq<int>>)
{
  forall i :: 0 <= i < |strs| ==> |p| <= |strs[i]| && forall k :: 0 <= k < |p| ==> p[k] == strs[i][k]
}

method LongestCommonPrefix(strs: seq<seq<int>>) returns (len: nat)
  requires |strs| > 0
  requires forall i :: 0 <= i < |strs| ==> |strs[i]| > 0
  ensures len <= |strs[0]|
  ensures IsCommonPrefix(strs[0][..len], strs)
  ensures forall l :: len < l <= |strs[0]| ==> !IsCommonPrefix(strs[0][..l], strs)
{
  len := |strs[0]|;
  var i := 1;
  while i < |strs|
    invariant 1 <= i <= |strs|
    invariant 0 <= len <= |strs[0]|
    invariant IsCommonPrefix(strs[0][..len], strs[..i])
    invariant forall l :: len < l <= |strs[0]| ==> !IsCommonPrefix(strs[0][..l], strs[..i])
    decreases |strs| - i
  {
    var j := 0;
    var minLen := if len < |strs[i]| then len else |strs[i]|;
    while j < minLen && strs[0][j] == strs[i][j]
      invariant 0 <= j <= minLen
      invariant forall k :: 0 <= k < j ==> strs[0][k] == strs[i][k]
      decreases minLen - j
    {
      j := j + 1;
    }
    // j is the common prefix length between strs[0][..len] and strs[i]
    // Any common prefix longer than j would disagree at position j
    assert j <= len;
    assert j <= |strs[i]|;

    // Update maximality proof for strs[..i+1]
    assert forall l :: j < l <= |strs[0]| ==> !IsCommonPrefix(strs[0][..l], strs[..i+1]) by {
      forall l | j < l <= |strs[0]|
        ensures !IsCommonPrefix(strs[0][..l], strs[..i+1])
      {
        if l <= len {
          // strs[0][..l] agrees with strs[0] on first l chars.
          // l > j means at position j: either j >= minLen or strs[0][j] != strs[i][j]
          assert strs[..i+1][i] == strs[i];
          if j < minLen {
            // strs[0][j] != strs[i][j], but strs[0][..l][j] == strs[0][j] since j < l
            assert strs[0][..l][j] == strs[0][j];
            assert strs[0][j] != strs[i][j];
          } else if j == len {
            // j == len < l, but strs[0][..l] has length l > len >= j = minLen
            // Actually j == minLen <= len < l.
            // If minLen == len then j == len < l, impossible since j <= len but l > j == len.
            // Wait: j == minLen, and minLen = min(len, |strs[i]|).
            // If minLen == |strs[i]| then l > j == |strs[i]|, so strs[0][..l] can't be prefix of strs[i]
            assert minLen == |strs[i]|;
            assert l > |strs[i]|;
          } else {
            // j == |strs[i]| < len, l > j, so l > |strs[i]|
            assert l > |strs[i]|;
          }
        } else {
          // l > len: not a common prefix of strs[..i] either
          assert !IsCommonPrefix(strs[0][..l], strs[..i]);
          assert !IsCommonPrefix(strs[0][..l], strs[..i+1]) by {
            if IsCommonPrefix(strs[0][..l], strs[..i+1]) {
              assert IsCommonPrefix(strs[0][..l], strs[..i]) by {
                forall m | 0 <= m < i
                  ensures |strs[0][..l]| <= |strs[..i][m]| && forall k :: 0 <= k < l ==> strs[0][..l][k] == strs[..i][m][k]
                {
                  assert strs[..i+1][m] == strs[..i][m];
                }
              }
            }
          }
        }
      }
    }

    len := j;

    assert IsCommonPrefix(strs[0][..len], strs[..i+1]) by {
      forall m {:trigger strs[..i+1][m]} | 0 <= m < i + 1
        ensures |strs[0][..len]| <= |strs[..i+1][m]| && forall k :: 0 <= k < len ==> strs[0][..len][k] == strs[..i+1][m][k]
      {
        if m < i {
          assert strs[..i+1][m] == strs[..i][m];
        } else {
          assert strs[..i+1][m] == strs[i];
        }
      }
    }

    i := i + 1;
  }
  assert strs[..|strs|] == strs;
}

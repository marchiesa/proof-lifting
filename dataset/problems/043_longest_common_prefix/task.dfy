// Longest Common Prefix of Array of Strings
// Task: Add loop invariants so that Dafny can verify this program.

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
  {
    var j := 0;
    var minLen := if len < |strs[i]| then len else |strs[i]|;
    while j < minLen && strs[0][j] == strs[i][j]
    {
      j := j + 1;
    }
    len := j;
    i := i + 1;
  }
}

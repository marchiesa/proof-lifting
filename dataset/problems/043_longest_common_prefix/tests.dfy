// Longest Common Prefix -- Test cases

predicate IsCommonPrefix(p: seq<int>, strs: seq<seq<int>>)
{
  forall i :: 0 <= i < |strs| ==> |p| <= |strs[i]| && forall k :: 0 <= k < |p| ==> p[k] == strs[i][k]
}

method {:axiom} LongestCommonPrefix(strs: seq<seq<int>>) returns (len: nat)
  requires |strs| > 0
  requires forall i :: 0 <= i < |strs| ==> |strs[i]| > 0
  ensures len <= |strs[0]|
  ensures IsCommonPrefix(strs[0][..len], strs)
  ensures forall l :: len < l <= |strs[0]| ==> !IsCommonPrefix(strs[0][..l], strs)

method TestCommon()
{
  // "abc", "abd", "abe" as int seqs
  var len := LongestCommonPrefix([[1, 2, 3], [1, 2, 4], [1, 2, 5]]);
  assert IsCommonPrefix([1, 2, 3][..len], [[1, 2, 3], [1, 2, 4], [1, 2, 5]]);
}

method TestAllSame()
{
  var len := LongestCommonPrefix([[1, 2, 3], [1, 2, 3]]);
  assert IsCommonPrefix([1, 2, 3][..len], [[1, 2, 3], [1, 2, 3]]);
}

method TestNoCommon()
{
  var len := LongestCommonPrefix([[1, 2], [3, 4]]);
  assert IsCommonPrefix([1, 2][..len], [[1, 2], [3, 4]]);
}

method TestSingle()
{
  var len := LongestCommonPrefix([[5, 6, 7]]);
  assert IsCommonPrefix([5, 6, 7][..len], [[5, 6, 7]]);
}

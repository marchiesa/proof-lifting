// Longest Common Prefix -- Runtime spec tests

predicate IsCommonPrefix(p: seq<int>, strs: seq<seq<int>>)
{
  forall i | 0 <= i < |strs| ::
    |p| <= |strs[i]| && forall k | 0 <= k < |p| :: p[k] == strs[i][k]
}

method Main() {
  // IsCommonPrefix positive cases
  expect IsCommonPrefix([1, 2], [[1, 2, 3], [1, 2, 4], [1, 2, 5]]),
    "[1,2] is common prefix of [[1,2,3],[1,2,4],[1,2,5]]";
  expect IsCommonPrefix([], [[1, 2], [3, 4]]),
    "empty is common prefix of anything";
  expect IsCommonPrefix([1, 2, 3], [[1, 2, 3], [1, 2, 3]]),
    "full string is common prefix when all same";
  expect IsCommonPrefix([5, 6, 7], [[5, 6, 7]]),
    "full string is prefix of single-element list";

  // IsCommonPrefix negative cases
  expect !IsCommonPrefix([1, 2, 3], [[1, 2, 3], [1, 2, 4]]),
    "[1,2,3] not common prefix when second differs at index 2";
  expect !IsCommonPrefix([1], [[2, 3], [1, 4]]),
    "[1] not prefix of [2,3]";
  expect !IsCommonPrefix([1, 2, 3, 4], [[1, 2, 3]]),
    "prefix longer than string";

  // Test longest property: the common prefix [1,2] is valid but [1,2,3] is not
  var strs := [[1, 2, 3], [1, 2, 4], [1, 2, 5]];
  expect IsCommonPrefix([1, 2], strs), "length-2 prefix valid";
  expect !IsCommonPrefix([1, 2, 3], strs), "length-3 prefix not valid";

  print "All spec tests passed\n";
}

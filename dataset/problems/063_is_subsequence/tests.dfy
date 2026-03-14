// Check if String is Subsequence -- Runtime spec tests

// The ghost predicate IsSubseq can't be executed at runtime.
// We provide a compilable version of IsSubseqFrom for testing.

method IsSubseqFromCheck(s: seq<int>, t: seq<int>, si: int, ti: int) returns (result: bool)
  requires 0 <= si <= |s|
  requires 0 <= ti <= |t|
  decreases |t| - ti
{
  if si == |s| { return true; }
  else if ti == |t| { return false; }
  else if s[si] == t[ti] { result := IsSubseqFromCheck(s, t, si + 1, ti + 1); }
  else { result := IsSubseqFromCheck(s, t, si, ti + 1); }
}

method IsSubseqCheck(s: seq<int>, t: seq<int>) returns (result: bool)
{
  result := IsSubseqFromCheck(s, t, 0, 0);
}

method Main()
{
  // Positive: [1,3] is a subsequence of [1,2,3,4]
  var r := IsSubseqCheck([1, 3], [1, 2, 3, 4]);
  expect r, "[1,3] should be subseq of [1,2,3,4]";

  // Positive: empty is subseq of anything
  r := IsSubseqCheck([], [1, 2, 3]);
  expect r, "[] should be subseq of [1,2,3]";

  // Positive: empty is subseq of empty
  r := IsSubseqCheck([], []);
  expect r, "[] should be subseq of []";

  // Positive: identical sequences
  r := IsSubseqCheck([1, 2, 3], [1, 2, 3]);
  expect r, "[1,2,3] should be subseq of [1,2,3]";

  // Positive: single match
  r := IsSubseqCheck([2], [1, 2, 3]);
  expect r, "[2] should be subseq of [1,2,3]";

  // Negative: [1] is not subseq of []
  r := IsSubseqCheck([1], []);
  expect !r, "[1] should not be subseq of []";

  // Negative: [4,1] order matters
  r := IsSubseqCheck([4, 1], [1, 2, 3, 4]);
  expect !r, "[4,1] should not be subseq of [1,2,3,4]";

  // Negative: element not present
  r := IsSubseqCheck([5], [1, 2, 3, 4]);
  expect !r, "[5] should not be subseq of [1,2,3,4]";

  // Negative: longer than source
  r := IsSubseqCheck([1, 2, 3, 4], [1, 2]);
  expect !r, "[1,2,3,4] should not be subseq of [1,2]";

  print "All spec tests passed\n";
}

// Count Distinct Subsequences -- Runtime spec tests

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

method Main()
{
  // NumDistinct: empty target always matches once
  expect NumDistinct([1, 2, 3], [], 0, 0) == 1, "Empty target = 1 match";
  expect NumDistinct([], [], 0, 0) == 1, "Both empty = 1 match";

  // NumDistinct: empty source, non-empty target = 0
  expect NumDistinct([], [1], 0, 0) == 0, "Empty source, non-empty target = 0";

  // NumDistinct: exact match
  expect NumDistinct([1, 2, 3], [1, 2, 3], 0, 0) == 1, "Exact match = 1";

  // NumDistinct: no match
  expect NumDistinct([1, 2], [3], 0, 0) == 0, "No matching element = 0";

  // NumDistinct: s = [1, 2, 1], t = [1, 1]
  // Subsequences: (pos 0, pos 2) -> 1 way
  expect NumDistinct([1, 2, 1], [1, 1], 0, 0) == 1, "[1,2,1] has 1 subseq matching [1,1]";

  // NumDistinct: s = [1, 1, 1], t = [1, 1]
  // Subsequences: (0,1), (0,2), (1,2) -> 3 ways
  expect NumDistinct([1, 1, 1], [1, 1], 0, 0) == 3, "[1,1,1] has 3 subseqs matching [1,1]";

  // NumDistinct: s = [1, 2, 1, 2], t = [1, 2]
  // Subsequences: (0,1), (0,3), (2,3) -> 3 ways
  expect NumDistinct([1, 2, 1, 2], [1, 2], 0, 0) == 3, "[1,2,1,2] has 3 subseqs matching [1,2]";

  // NumDistinct: target longer than source
  expect NumDistinct([1], [1, 2], 0, 0) == 0, "Target longer than source = 0";

  // NumDistinct: negative tests
  expect NumDistinct([1, 1, 1], [1, 1], 0, 0) != 2, "[1,1,1]->[1,1] != 2";
  expect NumDistinct([1, 2, 1, 2], [1, 2], 0, 0) != 2, "[1,2,1,2]->[1,2] != 2";

  // NumDistinct: partial match
  expect NumDistinct([1, 2, 3], [1, 3], 0, 0) == 1, "[1,2,3]->[1,3] = 1";
  expect NumDistinct([1, 2, 3], [2, 3], 0, 0) == 1, "[1,2,3]->[2,3] = 1";

  print "All spec tests passed\n";
}

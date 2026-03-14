// Simplified Regular Expression Matching -- Runtime spec tests

function Matches(s: seq<int>, p: seq<int>, si: int, pi: int): bool
  requires 0 <= si <= |s|
  requires 0 <= pi <= |p|
  decreases |p| - pi, |s| - si
{
  if pi == |p| then si == |s|
  else if pi + 1 < |p| && p[pi + 1] == -1 then
    Matches(s, p, si, pi + 2) ||
    (si < |s| && (p[pi] == 0 || p[pi] == s[si]) && Matches(s, p, si + 1, pi))
  else
    si < |s| && (p[pi] == 0 || p[pi] == s[si]) && Matches(s, p, si + 1, pi + 1)
}

method Main()
{
  // Exact match: positive
  expect Matches([1, 2], [1, 2], 0, 0), "[1,2] matches pattern [1,2]";
  expect Matches([1], [1], 0, 0), "[1] matches pattern [1]";

  // Exact match: negative
  expect !Matches([1], [2], 0, 0), "[1] does not match pattern [2]";
  expect !Matches([1, 2], [1], 0, 0), "[1,2] does not match pattern [1] (too long)";
  expect !Matches([1], [1, 2], 0, 0), "[1] does not match pattern [1,2] (too short)";

  // Dot (0) matches any: positive
  expect Matches([1], [0], 0, 0), "[1] matches [.] (dot)";
  expect Matches([5], [0], 0, 0), "[5] matches [.] (dot)";
  expect Matches([1, 2], [0, 0], 0, 0), "[1,2] matches [.,.]";

  // Star (-1): zero occurrences
  expect Matches([], [1, -1], 0, 0), "[] matches [a*] (zero occurrences)";

  // Star: one or more occurrences
  expect Matches([1], [1, -1], 0, 0), "[1] matches [1,*]";
  expect Matches([1, 1, 1], [1, -1], 0, 0), "[1,1,1] matches [1,*]";

  // Star: negative
  expect !Matches([2], [1, -1], 0, 0), "[2] does not match [1,*]";

  // Dot-star matches anything
  expect Matches([1, 2, 3], [0, -1], 0, 0), "[1,2,3] matches [.,*]";
  expect Matches([], [0, -1], 0, 0), "[] matches [.,*]";

  // Complex pattern
  // s = [1, 2], p = [1, 0] (a.)
  expect Matches([1, 2], [1, 0], 0, 0), "[1,2] matches [1,.]";
  expect !Matches([2, 2], [1, 0], 0, 0), "[2,2] does not match [1,.]";

  // Empty string and empty pattern
  expect Matches([], [], 0, 0), "[] matches []";
  expect !Matches([1], [], 0, 0), "[1] does not match []";
  expect !Matches([], [1], 0, 0), "[] does not match [1]";

  print "All spec tests passed\n";
}

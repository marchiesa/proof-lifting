// Wildcard Matching -- Runtime spec tests

function WildMatch(s: seq<int>, p: seq<int>, si: int, pi: int): bool
  requires 0 <= si <= |s|
  requires 0 <= pi <= |p|
  decreases |s| - si + |p| - pi
{
  if si == |s| && pi == |p| then true
  else if pi == |p| then false
  else if p[pi] == -1 then
    WildMatch(s, p, si, pi + 1) ||
    (si < |s| && WildMatch(s, p, si + 1, pi))
  else if si < |s| && (p[pi] == 0 || p[pi] == s[si]) then
    WildMatch(s, p, si + 1, pi + 1)
  else false
}

method Main()
{
  // Exact match: positive
  expect WildMatch([1, 2], [1, 2], 0, 0), "[1,2] matches [1,2]";
  expect WildMatch([1], [1], 0, 0), "[1] matches [1]";

  // Exact match: negative
  expect !WildMatch([1], [2], 0, 0), "[1] does not match [2]";
  expect !WildMatch([1, 2], [1, 3], 0, 0), "[1,2] does not match [1,3]";

  // Question mark (0) matches any single char
  expect WildMatch([1], [0], 0, 0), "[1] matches [?]";
  expect WildMatch([5], [0], 0, 0), "[5] matches [?]";
  expect WildMatch([1, 2], [0, 0], 0, 0), "[1,2] matches [?,?]";
  expect !WildMatch([1, 2], [0], 0, 0), "[1,2] does not match [?] (too long)";

  // Star (-1) matches any sequence (including empty)
  expect WildMatch([], [-1], 0, 0), "[] matches [*]";
  expect WildMatch([1], [-1], 0, 0), "[1] matches [*]";
  expect WildMatch([1, 2, 3], [-1], 0, 0), "[1,2,3] matches [*]";

  // Star with prefix/suffix
  expect WildMatch([1, 2, 3], [1, -1], 0, 0), "[1,2,3] matches [1,*]";
  expect WildMatch([1, 2, 3], [-1, 3], 0, 0), "[1,2,3] matches [*,3]";
  expect !WildMatch([1, 2, 3], [2, -1], 0, 0), "[1,2,3] does not match [2,*]";

  // Star in middle
  expect WildMatch([1, 2, 3], [1, -1, 3], 0, 0), "[1,2,3] matches [1,*,3]";
  expect WildMatch([1, 3], [1, -1, 3], 0, 0), "[1,3] matches [1,*,3]";

  // Multiple stars
  expect WildMatch([1, 2, 3], [-1, -1], 0, 0), "[1,2,3] matches [*,*]";

  // Empty cases
  expect WildMatch([], [], 0, 0), "[] matches []";
  expect !WildMatch([1], [], 0, 0), "[1] does not match []";
  expect !WildMatch([], [1], 0, 0), "[] does not match [1]";
  expect WildMatch([], [-1], 0, 0), "[] matches [*]";

  // Negative: star does not help wrong chars
  expect !WildMatch([1, 2, 3], [-1, 4], 0, 0), "[1,2,3] does not match [*,4]";

  print "All spec tests passed\n";
}

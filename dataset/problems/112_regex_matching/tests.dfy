// Simplified Regular Expression Matching -- Test cases
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

method {:axiom} RegexMatch(s: seq<int>, p: seq<int>) returns (result: bool)
  requires forall i :: 0 <= i < |s| ==> s[i] > 0
  ensures result == Matches(s, p, 0, 0)

method TestExactMatch() {
  // s = "ab" = [1,2], p = "ab" = [1,2]
  var r := RegexMatch([1, 2], [1, 2]);
  assert Matches([1, 2], [1, 2], 0, 0);
  assert r;
}

method TestStarEmpty() {
  // s = "", p = "a*" = [1, -1]
  var r := RegexMatch([], [1, -1]);
  assert Matches([], [1, -1], 0, 0);
  assert r;
}

method TestNoMatch() {
  // s = "a" = [1], p = "b" = [2]
  var r := RegexMatch([1], [2]);
  assert !Matches([1], [2], 0, 0);
  assert !r;
}

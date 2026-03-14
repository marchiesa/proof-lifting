// Wildcard Matching -- Test cases
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

method {:axiom} WildcardMatch(s: seq<int>, p: seq<int>) returns (result: bool)
  requires forall i :: 0 <= i < |s| ==> s[i] > 0
  ensures result == WildMatch(s, p, 0, 0)

method TestExact() {
  var r := WildcardMatch([1, 2], [1, 2]);
  assert WildMatch([1, 2], [1, 2], 0, 0);
  assert r;
}

method TestStar() {
  // s = [1], p = [*] = [-1]
  var r := WildcardMatch([1], [-1]);
  assert WildMatch([1], [-1], 0, 0);
  assert r;
}

method TestNoMatch() {
  var r := WildcardMatch([1], [2]);
  assert !WildMatch([1], [2], 0, 0);
  assert !r;
}

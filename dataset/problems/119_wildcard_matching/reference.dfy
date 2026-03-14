// Wildcard Matching -- Reference solution with invariants

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

// Recursive approach with memoization via ghost parameter
method WildcardMatchRec(s: seq<int>, p: seq<int>, si: int, pi: int)
  returns (result: bool)
  requires 0 <= si <= |s|
  requires 0 <= pi <= |p|
  requires forall i :: 0 <= i < |s| ==> s[i] > 0
  ensures result == WildMatch(s, p, si, pi)
  decreases |s| - si + |p| - pi
{
  if si == |s| && pi == |p| {
    result := true;
  } else if pi == |p| {
    result := false;
  } else if p[pi] == -1 {
    var r1 := WildcardMatchRec(s, p, si, pi + 1);
    if r1 {
      result := true;
    } else if si < |s| {
      result := WildcardMatchRec(s, p, si + 1, pi);
    } else {
      result := false;
    }
  } else if si < |s| && (p[pi] == 0 || p[pi] == s[si]) {
    result := WildcardMatchRec(s, p, si + 1, pi + 1);
  } else {
    result := false;
  }
}

method WildcardMatch(s: seq<int>, p: seq<int>) returns (result: bool)
  requires forall i :: 0 <= i < |s| ==> s[i] > 0
  ensures result == WildMatch(s, p, 0, 0)
{
  result := WildcardMatchRec(s, p, 0, 0);
}

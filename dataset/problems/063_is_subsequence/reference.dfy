// Check if String is Subsequence -- Reference solution with invariants

ghost predicate IsSubseqFrom(s: seq<int>, t: seq<int>, si: int, ti: int)
  requires 0 <= si <= |s|
  requires 0 <= ti <= |t|
  decreases |t| - ti
{
  if si == |s| then true
  else if ti == |t| then false
  else if s[si] == t[ti] then IsSubseqFrom(s, t, si + 1, ti + 1)
  else IsSubseqFrom(s, t, si, ti + 1)
}

ghost predicate IsSubseq(s: seq<int>, t: seq<int>)
{
  IsSubseqFrom(s, t, 0, 0)
}

method IsSubsequence(s: seq<int>, t: seq<int>) returns (result: bool)
  ensures result == IsSubseq(s, t)
{
  var i := 0;
  var j := 0;
  while j < |t| && i < |s|
    invariant 0 <= i <= |s|
    invariant 0 <= j <= |t|
    invariant IsSubseq(s, t) == IsSubseqFrom(s, t, i, j)
    decreases |t| - j
  {
    if s[i] == t[j] {
      i := i + 1;
    }
    j := j + 1;
  }
  result := i == |s|;
}

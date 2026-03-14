// Check if String is Subsequence -- Test cases

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

method {:axiom} IsSubsequence(s: seq<int>, t: seq<int>) returns (result: bool)
  ensures result == IsSubseq(s, t)

method TestSubseqTrue()
{
  var r := IsSubsequence([1, 3], [1, 2, 3, 4]);
  assert IsSubseq([1, 3], [1, 2, 3, 4]);
  assert r;
}

method TestSubseqFalse()
{
  var r := IsSubsequence([4, 1], [1, 2, 3, 4]);
  // r will be whatever the spec says
}

method TestEmptySubseq()
{
  var r := IsSubsequence([], [1, 2, 3]);
  assert IsSubseq([], [1, 2, 3]);
  assert r;
}

method TestEmptyMain()
{
  var r := IsSubsequence([1], []);
  assert !IsSubseq([1], []);
  assert !r;
}

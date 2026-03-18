ghost predicate IsSubsequence(c: seq<int>, s: seq<int>)
  decreases |s|
{
  if |c| == 0 then true
  else if |s| == 0 then false
  else if c[|c|-1] == s[|s|-1] then IsSubsequence(c[..|c|-1], s[..|s|-1])
  else IsSubsequence(c, s[..|s|-1])
}

ghost predicate ExistsCommonSubseqOfLen(a: seq<int>, b: seq<int>, k: nat)
  decreases |a| + |b|
{
  if k == 0 then true
  else if |a| == 0 || |b| == 0 then false
  else if a[|a|-1] == b[|b|-1] then
    ExistsCommonSubseqOfLen(a[..|a|-1], b[..|b|-1], k - 1) ||
    ExistsCommonSubseqOfLen(a[..|a|-1], b, k) ||
    ExistsCommonSubseqOfLen(a, b[..|b|-1], k)
  else
    ExistsCommonSubseqOfLen(a[..|a|-1], b, k) ||
    ExistsCommonSubseqOfLen(a, b[..|b|-1], k)
}

ghost function Min(x: nat, y: nat): nat {
  if x <= y then x else y
}

method CommonSubsequence(a: seq<int>, b: seq<int>) returns (found: bool, c: seq<int>)
  ensures found ==>
    |c| >= 1 &&
    IsSubsequence(c, a) &&
    IsSubsequence(c, b) &&
    forall len :: 1 <= len < |c| ==> !ExistsCommonSubseqOfLen(a, b, len)
  ensures !found ==>
    forall len :: 1 <= len <= Min(|a|, |b|) ==> !ExistsCommonSubseqOfLen(a, b, len)
{
  found := false;
  c := [];
  var i := 0;
  while i < |a|
  {
    var j := 0;
    while j < |b|
    {
      if a[i] == b[j] {
        found := true;
        c := [a[i]];
        return;
      }
      j := j + 1;
    }
    i := i + 1;
  }
}
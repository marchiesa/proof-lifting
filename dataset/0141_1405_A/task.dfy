ghost predicate InRange(s: seq<int>)
{
  forall i | 0 <= i < |s| :: 1 <= s[i] <= |s|
}

ghost predicate AllDistinct(s: seq<int>)
{
  forall i, j | 0 <= i < |s| && 0 <= j < |s| && i != j :: s[i] != s[j]
}

ghost predicate IsPermutation(p: seq<int>)
{
  InRange(p) && AllDistinct(p)
}

ghost function AdjacentSums(p: seq<int>): seq<int>
  decreases |p|
{
  if |p| < 2 then []
  else if |p| == 2 then [p[0] + p[1]]
  else [p[0] + p[1]] + AdjacentSums(p[1..])
}

ghost predicate SameFingerprint(p: seq<int>, q: seq<int>)
{
  multiset(AdjacentSums(p)) == multiset(AdjacentSums(q))
}

method PermutationForgery(p: seq<int>) returns (p': seq<int>)
  requires |p| >= 2
  requires IsPermutation(p)
  ensures |p'| == |p|
  ensures IsPermutation(p')
  ensures p' != p
  ensures SameFingerprint(p, p')
{
  p' := [];
  var i := |p|;
  while i > 0
  {
    i := i - 1;
    p' := p' + [p[i]];
  }
}
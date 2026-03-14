// Prefix Sum -- Reference solution with invariants

function Sum(a: seq<int>, lo: int, hi: int): int
  requires 0 <= lo <= hi <= |a|
  decreases hi - lo
{
  if lo == hi then 0
  else a[lo] + Sum(a, lo + 1, hi)
}

lemma SumExtend(a: seq<int>, lo: int, hi: int)
  requires 0 <= lo <= hi < |a|
  ensures Sum(a, lo, hi + 1) == Sum(a, lo, hi) + a[hi]
  decreases hi - lo
{
  if lo == hi {
  } else {
    SumExtend(a, lo + 1, hi);
  }
}

method PrefixSum(a: seq<int>) returns (p: seq<int>)
  ensures |p| == |a|
  ensures forall i :: 0 <= i < |p| ==> p[i] == Sum(a, 0, i + 1)
{
  if |a| == 0 {
    return [];
  }
  p := [a[0]];
  var i := 1;
  while i < |a|
    invariant 1 <= i <= |a|
    invariant |p| == i
    invariant forall j :: 0 <= j < i ==> p[j] == Sum(a, 0, j + 1)
    decreases |a| - i
  {
    SumExtend(a, 0, i);
    p := p + [p[i - 1] + a[i]];
    i := i + 1;
  }
}

// Prefix Sum
// Task: Add loop invariants so that Dafny can verify this program.

function Sum(a: seq<int>, lo: int, hi: int): int
  requires 0 <= lo <= hi <= |a|
  decreases hi - lo
{
  if lo == hi then 0
  else a[lo] + Sum(a, lo + 1, hi)
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
  {
    p := p + [p[i - 1] + a[i]];
    i := i + 1;
  }
}

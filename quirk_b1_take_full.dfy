function Sum(s: seq<int>): int {
  if |s| == 0 then 0 else Sum(s[..|s|-1]) + s[|s|-1]
}

method ComputeSum(a: seq<int>) returns (s: int)
  ensures s == Sum(a)
{
  s := 0;
  var i := 0;
  while i < |a|
    invariant 0 <= i <= |a|
    invariant s == Sum(a[..i])
  {
    assert a[..i+1][..i] == a[..i];
    s := s + a[i];
    i := i + 1;
  }
  assert a[..|a|] == a;
}

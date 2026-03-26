function Sum(s: seq<int>): int {
  if |s| == 0 then 0 else s[|s|-1] + Sum(s[..|s|-1])
}

method SumArray(a: seq<int>) returns (s: int)
  ensures s == Sum(a)
{
  s := 0;
  for i := 0 to |a|
    invariant s == Sum(a[..i])
  {
    assert a[..i + 1][..i] == a[..i];
    s := s + a[i];
  }
}

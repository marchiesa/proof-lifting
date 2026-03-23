method M(a: seq<int>) returns (s: int)
  ensures s == Sum(a)
{
  s := 0;
  var i := 0;
  while i < |a|
    invariant 0 <= i <= |a|
    invariant s == Sum(a[..i])
  {
    assert Sum(a[..i+1]) == Sum(a[..i]) + a[i];
    s := s + a[i];
    i := i + 1;
  }
  assert a[..|a|] == a;
}
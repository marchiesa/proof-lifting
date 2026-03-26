method Copy(a: seq<int>) returns (r: seq<int>)
  ensures r == a
{
  r := [];
  var i := 0;
  while i < |a|
    invariant 0 <= i <= |a|
    invariant r == a[..i]
  {
    r := r + [a[i]];
    i := i + 1;
  }
  assert a[..|a|] == a;
}

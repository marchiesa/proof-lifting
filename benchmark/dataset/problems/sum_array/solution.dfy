// Reference solution

function Sum(s: seq<int>): int
{
  if |s| == 0 then 0
  else s[0] + Sum(s[1..])
}

method SumArray(s: seq<int>) returns (r: int)
  ensures r == Sum(s)
{
  r := 0;
  var i := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant r == Sum(s[..i])
  {
    assert s[..i+1] == s[..i] + [s[i]];
    r := r + s[i];
    i := i + 1;
  }
  assert s[..|s|] == s;
}

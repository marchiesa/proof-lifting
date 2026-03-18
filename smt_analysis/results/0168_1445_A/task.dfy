ghost predicate CanRearrange(a: seq<int>, b: seq<int>, x: int)
  requires |a| == |b|
  decreases |a|
{
  if |a| == 0 then true
  else exists j | 0 <= j < |b| ::
    a[0] + b[j] <= x &&
    CanRearrange(a[1..], b[..j] + b[j+1..], x)
}

method ArrayRearrangement(a: seq<int>, b: seq<int>, x: int) returns (result: bool)
  requires |a| == |b|
  ensures result == CanRearrange(a, b, x)
{
  var n := |a|;
  var i := 0;
  while i < n
  {
    if a[i] + b[n - 1 - i] > x {
      return false;
    }
    i := i + 1;
  }
  return true;
}
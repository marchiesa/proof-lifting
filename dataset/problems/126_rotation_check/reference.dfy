// Rotation Check -- Reference solution with invariants

predicate IsRotation(a: seq<int>, b: seq<int>)
{
  |a| == |b| &&
  exists k :: 0 <= k <= |a| && b == a[k..] + a[..k]
}

method CheckRotation(a: seq<int>, b: seq<int>) returns (result: bool)
  ensures result == IsRotation(a, b)
{
  if |a| != |b| {
    return false;
  }
  if |a| == 0 {
    assert b == a[0..] + a[..0];
    return true;
  }
  var k := 0;
  while k < |a|
    invariant 0 <= k <= |a|
    invariant forall j :: 0 <= j < k ==> b != a[j..] + a[..j]
    decreases |a| - k
  {
    if b == a[k..] + a[..k] {
      return true;
    }
    k := k + 1;
  }
  // k == |a|, check rotation by |a| which equals rotation by 0
  assert a[|a|..] + a[..|a|] == a;
  assert a[0..] + a[..0] == a;
  // All k from 0 to |a|-1 failed, and rotation by |a| equals rotation by 0
  return false;
}

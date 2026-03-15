// Rotation Check
// Task: Add loop invariants so that Dafny can verify this program.
// Check if one sequence is a rotation of another.

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
    return true;
  }
  var k := 0;
  while k < |a|
  {
    if b == a[k..] + a[..k] {
      return true;
    }
    k := k + 1;
  }
  return false;
}

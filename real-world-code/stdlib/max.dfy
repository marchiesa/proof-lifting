// Find maximum element — every standard library has this
// (Rust: Iterator::max, Python: max(), Java: Collections.max)
//
// Invariant combines slicing (m is in prefix) with quantifiers (m >= all seen).

method Max(a: seq<int>) returns (m: int)
  requires |a| > 0
  ensures m in a
  ensures forall i :: 0 <= i < |a| ==> m >= a[i]
{
  m := a[0];
  var i := 1;
  while i < |a|
    invariant 1 <= i <= |a|
    invariant m in a[..i]
    invariant forall j :: 0 <= j < i ==> m >= a[j]
  {
    if a[i] > m {
      m := a[i];
    }
    i := i + 1;
  }
}

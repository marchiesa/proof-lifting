// Linear search — exists in every standard library
// (Rust: slice::contains, Python: `x in list`, Java: List.contains)
//
// Simplest possible code. Invariant uses slicing.

method Contains(a: seq<int>, target: int) returns (found: bool)
  ensures found == (target in a)
{
  var i := 0;
  while i < |a|
    invariant 0 <= i <= |a|
    invariant target !in a[..i]
  {
    if a[i] == target { return true; }
    i := i + 1;
  }
  return false;
}

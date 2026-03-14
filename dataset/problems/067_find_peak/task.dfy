// Find Peak Element
// Task: Add loop invariants so that Dafny can verify this program.

predicate IsPeak(a: array<int>, i: int)
  reads a
  requires 0 <= i < a.Length
{
  (i == 0 || a[i] > a[i - 1]) && (i == a.Length - 1 || a[i] > a[i + 1])
}

method FindPeak(a: array<int>) returns (p: int)
  requires a.Length >= 1
  requires forall i, j :: 0 <= i < j < a.Length ==> a[i] != a[j]
  ensures 0 <= p < a.Length
  ensures IsPeak(a, p)
{
  if a.Length == 1 {
    return 0;
  }
  if a[0] > a[1] {
    return 0;
  }
  if a[a.Length - 1] > a[a.Length - 2] {
    return a.Length - 1;
  }
  var i := 1;
  while i < a.Length - 1
  {
    if a[i] > a[i - 1] && a[i] > a[i + 1] {
      return i;
    }
    i := i + 1;
  }
  // unreachable if distinct elements guaranteed
  return 0; // dummy
}

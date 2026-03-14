// Find Peak Element -- Reference solution with invariants

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
  // At this point: a[0] < a[1] and a[n-1] < a[n-2]
  // So there's an interior peak
  var i := 1;
  while i < a.Length - 1
    invariant 1 <= i <= a.Length - 1
    invariant a[i - 1] < a[i]  // ascending at left boundary
    decreases a.Length - i
  {
    if a[i] > a[i + 1] {
      // a[i-1] < a[i] and a[i] > a[i+1], so i is a peak
      return i;
    }
    // a[i] <= a[i+1], but since distinct, a[i] < a[i+1]
    assert a[i] != a[i + 1];
    i := i + 1;
  }
  // i == a.Length - 1, and a[i-1] < a[i], i.e. a[n-2] < a[n-1]
  // But we checked a[n-1] < a[n-2] above -- contradiction
  assert a[a.Length - 2] < a[a.Length - 1];
  assert a[a.Length - 1] < a[a.Length - 2];
  return 0; // unreachable
}

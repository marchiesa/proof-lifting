// Maximum Width Ramp -- Reference solution with invariants

function Max(a: int, b: int): int { if a >= b then a else b }

method MaxWidthRamp(a: seq<int>) returns (maxWidth: int)
  requires |a| >= 2
  ensures maxWidth >= 0
  ensures maxWidth > 0 ==> exists i, j :: 0 <= i < j < |a| && a[i] <= a[j] && j - i == maxWidth
{
  maxWidth := 0;
  var i := 0;
  while i < |a|
    invariant 0 <= i <= |a|
    invariant maxWidth >= 0
    invariant maxWidth > 0 ==> exists p, q :: 0 <= p < q < |a| && a[p] <= a[q] && q - p == maxWidth
    decreases |a| - i
  {
    var j := i + 1;
    while j < |a|
      invariant i + 1 <= j <= |a|
      invariant maxWidth >= 0
      invariant maxWidth > 0 ==> exists p, q :: 0 <= p < q < |a| && a[p] <= a[q] && q - p == maxWidth
      decreases |a| - j
    {
      if a[i] <= a[j] && j - i > maxWidth {
        maxWidth := j - i;
      }
      j := j + 1;
    }
    i := i + 1;
  }
}

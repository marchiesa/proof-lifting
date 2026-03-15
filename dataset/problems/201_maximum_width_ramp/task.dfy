// Maximum Width Ramp
// Task: Add loop invariants so that Dafny can verify this program.

predicate IsRamp(a: seq<int>, i: int, j: int)
  requires 0 <= i < |a| && 0 <= j < |a|
{
  i < j && a[i] <= a[j]
}

function Max(a: int, b: int): int { if a >= b then a else b }

method MaxWidthRamp(a: seq<int>) returns (maxWidth: int)
  requires |a| >= 2
  ensures maxWidth >= 0
  ensures maxWidth > 0 ==> exists i, j :: 0 <= i < j < |a| && a[i] <= a[j] && j - i == maxWidth
{
  maxWidth := 0;
  var i := 0;
  while i < |a|
  {
    var j := i + 1;
    while j < |a|
    {
      if a[i] <= a[j] && j - i > maxWidth {
        maxWidth := j - i;
      }
      j := j + 1;
    }
    i := i + 1;
  }
}

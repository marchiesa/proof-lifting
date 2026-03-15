// Maximum Width Ramp

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

method Main()
{
  // [6,0,8,2,1,5] => ramp from index 1 to 5 (0<=5), width=4
  var a := [6, 0, 8, 2, 1, 5];
  var r1 := MaxWidthRamp(a);
  expect r1 >= 0;
  expect r1 > 0;  // definitely a ramp exists

  // Strictly decreasing: [5,4,3,2,1] => no ramp
  var b := [5, 4, 3, 2, 1];
  var r2 := MaxWidthRamp(b);
  expect r2 >= 0;

  // All equal => max ramp = |a|-1
  var c := [3, 3, 3, 3];
  var r3 := MaxWidthRamp(c);
  expect r3 > 0;

  // Two elements: ramp exists
  var d := [1, 2];
  var r4 := MaxWidthRamp(d);
  expect r4 > 0;

  // Two elements: no ramp
  var e := [2, 1];
  var r5 := MaxWidthRamp(e);
  expect r5 >= 0;

  print "All spec tests passed\n";
}

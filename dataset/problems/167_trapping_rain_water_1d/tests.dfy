// Trapping Rain Water 1D -- Spec tests

function Min(a: int, b: int): int { if a <= b then a else b }
function Max(a: int, b: int): int { if a >= b then a else b }

method TrappingRainWater(height: seq<int>) returns (result: int)
  requires |height| > 0
  requires forall i :: 0 <= i < |height| ==> height[i] >= 0
  ensures result >= 0
{
  var n := |height|;
  var leftMax := new int[n];
  var rightMax := new int[n];
  leftMax[0] := height[0];
  var i := 1;
  while i < n invariant 1 <= i <= n decreases n - i { leftMax[i] := Max(leftMax[i-1], height[i]); i := i + 1; }
  rightMax[n-1] := height[n-1];
  i := n - 2;
  while i >= 0 invariant -1 <= i <= n - 2 decreases i + 1 { rightMax[i] := Max(rightMax[i+1], height[i]); i := i - 1; }
  result := 0;
  i := 0;
  while i < n invariant 0 <= i <= n invariant result >= 0 decreases n - i {
    result := result + Max(0, Min(leftMax[i], rightMax[i]) - height[i]);
    i := i + 1;
  }
}

method Main() {
  var r1 := TrappingRainWater([0, 1, 0, 2, 1, 0, 1, 3, 2, 1, 2, 1]);
  expect r1 == 6;

  var r2 := TrappingRainWater([4, 2, 0, 3, 2, 5]);
  expect r2 == 9;

  // No water: flat
  var r3 := TrappingRainWater([1, 1, 1]);
  expect r3 == 0;

  // No water: strictly increasing
  var r4 := TrappingRainWater([1, 2, 3]);
  expect r4 == 0;

  // Negative: result always >= 0
  expect r3 >= 0;

  print "All spec tests passed\n";
}

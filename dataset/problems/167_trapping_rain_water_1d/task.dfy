// Trapping Rain Water 1D
// Task: Add loop invariants so that Dafny can verify this program.

function Min(a: int, b: int): int { if a <= b then a else b }
function Max(a: int, b: int): int { if a >= b then a else b }

// Water at position i = max(0, min(maxLeft, maxRight) - height[i])
function WaterAt(height: seq<int>, leftMax: seq<int>, rightMax: seq<int>, i: int): int
  requires 0 <= i < |height| == |leftMax| == |rightMax|
{
  Max(0, Min(leftMax[i], rightMax[i]) - height[i])
}

predicate IsTrappedWater(height: seq<int>, result: int, leftMax: seq<int>, rightMax: seq<int>)
  requires |height| > 0
  requires |leftMax| == |rightMax| == |height|
{
  // leftMax[i] is max of height[0..i]
  (forall i :: 0 <= i < |height| ==> leftMax[i] >= height[i]) &&
  // rightMax[i] is max of height[i..|height|]
  (forall i :: 0 <= i < |height| ==> rightMax[i] >= height[i]) &&
  result >= 0
}

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
  while i < n
  {
    leftMax[i] := Max(leftMax[i-1], height[i]);
    i := i + 1;
  }

  rightMax[n-1] := height[n-1];
  i := n - 2;
  while i >= 0
  {
    rightMax[i] := Max(rightMax[i+1], height[i]);
    i := i - 1;
  }

  result := 0;
  i := 0;
  while i < n
  {
    result := result + Max(0, Min(leftMax[i], rightMax[i]) - height[i]);
    i := i + 1;
  }
}

// Trapping Rain Water 1D -- Reference solution with invariants

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
  while i < n
    invariant 1 <= i <= n
    invariant leftMax[0] == height[0]
    invariant forall k :: 0 <= k < i ==> leftMax[k] >= height[k]
    invariant forall k :: 0 <= k < i ==> leftMax[k] >= 0
    decreases n - i
  {
    leftMax[i] := Max(leftMax[i-1], height[i]);
    i := i + 1;
  }

  rightMax[n-1] := height[n-1];
  i := n - 2;
  while i >= 0
    invariant -1 <= i <= n - 2
    invariant rightMax[n-1] == height[n-1]
    invariant forall k :: i < k < n ==> rightMax[k] >= height[k]
    invariant forall k :: i < k < n ==> rightMax[k] >= 0
    decreases i + 1
  {
    rightMax[i] := Max(rightMax[i+1], height[i]);
    i := i - 1;
  }

  result := 0;
  i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant result >= 0
    decreases n - i
  {
    result := result + Max(0, Min(leftMax[i], rightMax[i]) - height[i]);
    i := i + 1;
  }
}

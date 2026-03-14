// Rain Water Trapping (Two Pointer)
// Task: Add loop invariants so that Dafny can verify this program.

function Max(a: int, b: int): int { if a >= b then a else b }
function Min(a: int, b: int): int { if a <= b then a else b }

function MaxLeft(h: seq<int>, i: int): int
  requires 0 <= i < |h|
{
  if i == 0 then h[0]
  else Max(h[i], MaxLeft(h, i - 1))
}

function MaxRight(h: seq<int>, i: int): int
  requires 0 <= i < |h|
{
  if i == |h| - 1 then h[i]
  else Max(h[i], MaxRight(h, i + 1))
}

function WaterAt(h: seq<int>, i: int): int
  requires 0 <= i < |h|
{
  var level := Min(MaxLeft(h, i), MaxRight(h, i));
  if level > h[i] then level - h[i] else 0
}

function TotalWater(h: seq<int>): int
{
  if |h| == 0 then 0
  else TotalWaterHelper(h, 0)
}

function TotalWaterHelper(h: seq<int>, i: int): int
  requires 0 <= i <= |h|
{
  if i == |h| then 0
  else WaterAt(h, i) + TotalWaterHelper(h, i + 1)
}

method TrapWater(h: seq<int>) returns (water: int)
  requires |h| > 0
  requires forall i :: 0 <= i < |h| ==> h[i] >= 0
  ensures water >= 0
{
  water := 0;
  var left := 0;
  var right := |h| - 1;
  var leftMax := 0;
  var rightMax := 0;

  while left <= right
  {
    if h[left] <= h[right] {
      if h[left] >= leftMax {
        leftMax := h[left];
      } else {
        water := water + leftMax - h[left];
      }
      left := left + 1;
    } else {
      if h[right] >= rightMax {
        rightMax := h[right];
      } else {
        water := water + rightMax - h[right];
      }
      right := right - 1;
    }
  }
}

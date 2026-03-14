// Rain Water Trapping (Two Pointer) -- Reference solution with invariants

function Max(a: int, b: int): int { if a >= b then a else b }
function Min(a: int, b: int): int { if a <= b then a else b }

// Simpler spec: compute water using leftMax/rightMax arrays
function MaxFromLeft(h: seq<int>, i: int): int
  requires 0 <= i < |h|
{
  if i == 0 then h[0]
  else Max(h[i], MaxFromLeft(h, i - 1))
}

function MaxFromRight(h: seq<int>, i: int): int
  requires 0 <= i < |h|
  decreases |h| - i
{
  if i == |h| - 1 then h[i]
  else Max(h[i], MaxFromRight(h, i + 1))
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
    invariant 0 <= left
    invariant right < |h|
    invariant left <= right + 1
    invariant leftMax >= 0
    invariant rightMax >= 0
    invariant water >= 0
    invariant left > 0 ==> leftMax >= h[left - 1]
    invariant right < |h| - 1 ==> rightMax >= h[right + 1]
    invariant forall i :: 0 <= i < left ==> leftMax >= h[i]
    invariant forall i :: right < i < |h| ==> rightMax >= h[i]
    decreases right - left + 1
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

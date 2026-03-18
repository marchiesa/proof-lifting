// --- Specification: models the problem's operations ---

// Power of 2
ghost function Pow2(n: nat): nat
  decreases n
{
  if n == 0 then 1 else 2 * Pow2(n - 1)
}

// Get bit i of mask (0-indexed from LSB)
ghost function GetBit(mask: nat, i: nat): bool
{
  (mask / Pow2(i)) % 2 == 1
}

// Count selected elements in positions 0..n-1
ghost function MaskSelectedCount(mask: nat, n: nat): nat
  decreases n
{
  if n == 0 then 0
  else MaskSelectedCount(mask, n - 1) + (if GetBit(mask, n - 1) then 1 else 0)
}

// Sum of elements selected by mask
ghost function SubseqSum(a: seq<int>, mask: nat): int
  decreases |a|
{
  if |a| == 0 then 0
  else
    SubseqSum(a[..|a|-1], mask) + (if GetBit(mask, (|a| - 1) as nat) then a[|a|-1] else 0)
}

// Apply one operation: select a subsequence via bitmask, remove elements strictly above its average.
// Uses the equivalence: a[i] > sum/count  <==>  a[i]*count > sum  (for count > 0).
ghost function PerformOp(a: seq<int>, mask: nat): seq<int>
{
  var c := MaskSelectedCount(mask, |a| as nat);
  if c == 0 then a
  else
    var s := SubseqSum(a, mask);
    RemoveAboveAvg(a, mask, s, c)
}

// Keep elements that are either not selected, or not strictly above the subsequence average.
ghost function RemoveAboveAvg(a: seq<int>, mask: nat, total: int, count: nat): seq<int>
  requires count > 0
  decreases |a|
{
  if |a| == 0 then []
  else
    var i: nat := (|a| - 1) as nat;
    var rest := RemoveAboveAvg(a[..|a|-1], mask, total, count);
    var selected := GetBit(mask, i);
    var aboveAvg := a[i] * (count as int) > total;
    if selected && aboveAvg then rest else rest + [a[i]]
}

// Can we reduce array `a` to exactly `sz` elements by performing at most `steps` operations?
// Each operation chooses a non-empty subsequence and deletes elements strictly above its average.
// Non-productive operations (that delete nothing) are skipped since they don't change the array.
ghost predicate CanReachSize(a: seq<int>, sz: int, steps: nat)
  decreases steps
{
  if |a| == sz then true
  else if |a| < sz || sz < 0 then false
  else if steps == 0 then false
  else
    exists mask: nat | mask >= 1 ::
      var next := PerformOp(a, mask);
      |next| < |a| &&
      CanReachSize(next, sz, steps - 1)
}

method EshagLovesBigArrays(a: seq<int>) returns (deleted: int)
  requires |a| >= 1
  ensures 0 <= deleted <= |a|
  ensures CanReachSize(a, |a| - deleted, |a| as nat)
  ensures forall k: int {:trigger CanReachSize(a, |a| - k, |a| as nat)} | deleted < k <= |a| :: !CanReachSize(a, |a| - k, |a| as nat)
{
  var mi := a[0];
  var i := 1;
  while i < |a|
  {
    if a[i] < mi {
      mi := a[i];
    }
    i := i + 1;
  }

  var c := 0;
  i := 0;
  while i < |a|
  {
    if a[i] == mi {
      c := c + 1;
    }
    i := i + 1;
  }

  deleted := |a| - c;
}
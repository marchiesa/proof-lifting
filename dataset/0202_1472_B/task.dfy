// --- Specification: models the problem structure ---

// Sum of all candy weights
ghost function Sum(a: seq<int>): int
  decreases |a|
{
  if |a| == 0 then 0 else Sum(a[..|a|-1]) + a[|a|-1]
}

// 2^exp: size of the assignment space for exp candies
ghost function Pow2(exp: nat): nat
  decreases exp
{
  if exp == 0 then 1 else 2 * Pow2(exp - 1)
}

// Extract bit i from a bitmask (0 = least significant)
ghost function Bit(mask: nat, i: nat): bool
  decreases i
{
  if i == 0 then mask % 2 == 1
  else Bit(mask / 2, i - 1)
}

// Total weight of candies assigned to Alice (bit = 1) under assignment `mask`
ghost function AliceWeight(a: seq<int>, mask: nat): int
  decreases |a|
{
  if |a| == 0 then 0
  else AliceWeight(a[..|a|-1], mask) + (if Bit(mask, |a| - 1) then a[|a|-1] else 0)
}

// Total weight of candies assigned to Bob (bit = 0) under assignment `mask`
ghost function BobWeight(a: seq<int>, mask: nat): int
  decreases |a|
{
  if |a| == 0 then 0
  else BobWeight(a[..|a|-1], mask) + (if !Bit(mask, |a| - 1) then a[|a|-1] else 0)
}

// There exists an assignment of all candies to Alice and Bob
// such that Alice's total weight equals Bob's total weight
ghost predicate CanDivideFairly(a: seq<int>)
{
  exists mask: nat ::
    AliceWeight(a, mask) == BobWeight(a, mask)
}

// --- Method with specification ---

method FairDivision(a: seq<int>) returns (result: bool)
  requires forall i | 0 <= i < |a| :: a[i] == 1 || a[i] == 2
  ensures result == CanDivideFairly(a)
{
  var s := 0;
  var count1 := 0;
  var count2 := 0;
  var i := 0;
  while i < |a|
  {
    s := s + a[i];
    if a[i] == 1 {
      count1 := count1 + 1;
    }
    if a[i] == 2 {
      count2 := count2 + 1;
    }
    i := i + 1;
  }
  if s % 2 == 1 {
    return false;
  }
  if count2 % 2 == 1 && count1 == 0 {
    return false;
  }
  return true;
}
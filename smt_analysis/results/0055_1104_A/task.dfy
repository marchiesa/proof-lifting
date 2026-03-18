// === Specification predicates and functions ===

ghost function Sum(a: seq<int>): int
  decreases |a|
{
  if |a| == 0 then 0 else a[|a| - 1] + Sum(a[..|a| - 1])
}

ghost predicate AllInRange(a: seq<int>, lo: int, hi: int)
{
  forall i | 0 <= i < |a| :: lo <= a[i] <= hi
}

ghost function DistinctSet(a: seq<int>): set<int>
  decreases |a|
{
  if |a| == 0 then {} else {a[|a| - 1]} + DistinctSet(a[..|a| - 1])
}

ghost function CountDistinct(a: seq<int>): int
{
  |DistinctSet(a)|
}

// A valid splitting of n: non-empty sequence of digits 1..9 summing to n
ghost predicate IsValidSplitting(a: seq<int>, n: int)
{
  |a| >= 1 && AllInRange(a, 1, 9) && Sum(a) == n
}

ghost function Pow2(e: int): int
  requires e >= 0
  ensures Pow2(e) >= 1
  decreases e
{
  if e == 0 then 1 else 2 * Pow2(e - 1)
}

ghost function PopCount(mask: int): int
  requires mask >= 0
  ensures PopCount(mask) >= 0
  decreases mask
{
  if mask == 0 then 0 else PopCount(mask / 2) + mask % 2
}

// Can n be expressed as a non-negative integer combination of the
// digit values v..9 whose bits are set in mask?
// Bit (v-1) of mask indicates whether digit value v is allowed.
ghost predicate CanMakeSumFrom(n: int, mask: int, v: int)
  requires n >= 0 && mask >= 0 && 1 <= v <= 10
  decreases 10 - v
{
  if v == 10 then
    n == 0
  else if (mask / Pow2(v - 1)) % 2 == 0 then
    CanMakeSumFrom(n, mask, v + 1)
  else
    exists c | 0 <= c <= n / v :: CanMakeSumFrom(n - c * v, mask, v + 1)
}

// Can n be expressed as a sum of digits from the subset of {1..9} encoded by mask?
ghost predicate CanMakeSum(n: int, mask: int)
  requires n >= 0 && 0 <= mask < 512
{
  CanMakeSumFrom(n, mask, 1)
}

// Can n be split into digits 1..9 using at most d distinct digit values?
ghost predicate CanSplitWithAtMost(n: int, d: int)
  requires n >= 0
{
  exists mask | 0 <= mask < 512 ::
    PopCount(mask) <= d && CanMakeSum(n, mask)
}

// === Method with formal specification ===

method SplitIntoDigits(n: int) returns (k: int, digits: seq<int>)
  requires n >= 1
  ensures k == |digits|
  ensures IsValidSplitting(digits, n)
  ensures !CanSplitWithAtMost(n, CountDistinct(digits) - 1)
{
  k := n;
  digits := seq(n, _ => 1);
}
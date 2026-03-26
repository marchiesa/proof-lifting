// ──────────────────────────────────────────
// Specification: Phoenix and Balance
// ──────────────────────────────────────────

// 2^k as a pure function
ghost function Pow2Func(k: int): int
  requires k >= 0
  decreases k
{
  if k == 0 then 1 else 2 * Pow2Func(k - 1)
}

// Absolute value
ghost function Abs(x: int): int {
  if x >= 0 then x else -x
}

// Whether bit i is set in the binary representation of mask
ghost predicate BitIsSet(mask: int, i: int)
  requires mask >= 0
  requires i >= 0
{
  (mask / Pow2Func(i)) % 2 == 1
}

// Count of set bits in positions 0..n-1
ghost function CountSetBits(mask: int, n: int): int
  requires mask >= 0
  requires n >= 0
  decreases n
{
  if n == 0 then 0
  else CountSetBits(mask, n - 1) + (if BitIsSet(mask, n - 1) then 1 else 0)
}

// A valid split of coins 2^1..2^n into two piles of exactly n/2 each.
// Encoded as a bitmask: bit j set means coin j (0-indexed, weight 2^{j+1})
// goes to pile 1; bit j clear means it goes to pile 2.
ghost predicate ValidSplit(mask: int, n: int)
  requires mask >= 0
  requires n >= 0
  requires n % 2 == 0
{
  mask < Pow2Func(n) && CountSetBits(mask, n) == n / 2
}

// Signed weight difference (pile1_sum - pile2_sum) for a given split.
// Coin j (0-indexed) has weight 2^{j+1}.
ghost function SplitDiff(mask: int, n: int): int
  requires mask >= 0
  requires n >= 0
  decreases n
{
  if n == 0 then 0
  else
    SplitDiff(mask, n - 1) +
    (if BitIsSet(mask, n - 1) then Pow2Func(n) else -Pow2Func(n))
}

// diff is the minimum |pile1_sum - pile2_sum| over all ways to split
// coins 2^1, 2^2, ..., 2^n into two piles of n/2 coins each
ghost predicate IsMinDiff(diff: int, n: int)
  requires n >= 2
  requires n % 2 == 0
{
  diff >= 0
  // Some valid split achieves exactly this difference
  && (exists mask: int | 0 <= mask < Pow2Func(n) ::
       ValidSplit(mask, n) && Abs(SplitDiff(mask, n)) == diff)
  // No valid split achieves a smaller difference
  && (forall mask: int :: 0 <= mask < Pow2Func(n) ==>
       ValidSplit(mask, n) ==> Abs(SplitDiff(mask, n)) >= diff)
}

// ──────────────────────────────────────────
// Implementation
// ──────────────────────────────────────────

method Pow2(exp: int) returns (result: int)
  requires exp >= 0
  ensures result == Pow2Func(exp)
{
  result := 1;
  var i := 0;
  while i < exp {
    result := result * 2;
    i := i + 1;
  }
}

method PhoenixAndBalance(n: int) returns (diff: int)
  requires n >= 2 && n % 2 == 0
  ensures IsMinDiff(diff, n)
{
  var powNPlus1 := Pow2(n + 1);
  var total := powNPlus1 - 2;
  var powNHalf := Pow2(n / 2);
  var powN := Pow2(n);
  var left := powNHalf - 2 + powN;
  var right := total - left;
  diff := left - right;
}
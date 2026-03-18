// Number of digits in a positive integer
ghost function NumDigits(n: int): int
  requires n >= 1
  decreases n
{
  if n < 10 then 1 else 1 + NumDigits(n / 10)
}

// RepUnit(k) = 111...1 (k ones) — the repeating-ones template
ghost function RepUnit(k: int): int
  requires 1 <= k <= 4
{
  if k == 1 then 1 else 10 * RepUnit(k - 1) + 1
}

// The boring apartment number formed by repeating digit d exactly k times
ghost function BoringNum(d: int, k: int): int
  requires 1 <= d <= 9 && 1 <= k <= 4
{
  d * RepUnit(k)
}

// x is a boring apartment if it equals BoringNum(d, k) for some valid d, k
ghost predicate IsBoringApartment(x: int)
{
  exists d {:trigger BoringNum(d, 1)} | 1 <= d <= 9 ::
    exists k {:trigger BoringNum(d, k)} | 1 <= k <= 4 :: x == BoringNum(d, k)
}

// Total keypresses when calling all boring apartments in order
// (1,1), (1,2), (1,3), (1,4), (2,1), ..., up to and including (d, k).
// Each apartment contributes NumDigits(its number) keypresses.
ghost function TotalKeypresses(d: int, k: int): int
  requires 1 <= d <= 9 && 1 <= k <= 4
  decreases 4 * (d - 1) + (k - 1)
{
  var cost := NumDigits(BoringNum(d, k));
  if d == 1 && k == 1 then cost
  else if k > 1 then TotalKeypresses(d, k - 1) + cost
  else TotalKeypresses(d - 1, 4) + cost
}

method BoringApartments(x: int) returns (keypresses: int)
  requires IsBoringApartment(x)
  ensures exists d {:trigger BoringNum(d, 1)} | 1 <= d <= 9 ::
    exists k {:trigger BoringNum(d, k)} | 1 <= k <= 4 ::
    x == BoringNum(d, k) && keypresses == TotalKeypresses(d, k)
{
  // ... original body unchanged ...
}
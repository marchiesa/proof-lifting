ghost function NumDigits(n: int): nat
  requires n > 0
  decreases n
{
  if n < 10 then 1 else 1 + NumDigits(n / 10)
}

ghost function Pow2(d: nat): nat
  decreases d
{
  if d == 0 then 1 else 2 * Pow2(d - 1)
}

// Interprets the binary representation of i as a decimal number.
// This bijectively enumerates all binary decimals (positive integers
// whose decimal digits are all 0 or 1).
// E.g., 5 (binary 101) -> 101, 7 (binary 111) -> 111
ghost function BinToDec(i: nat): nat
  decreases i
{
  if i == 0 then 0
  else BinToDec(i / 2) * 10 + i % 2
}

// Can n be expressed as a sum of exactly k binary decimals?
// Binary decimals are enumerated as BinToDec(i) for 1 <= i < bdBound.
ghost predicate CanDecompose(n: int, k: nat, bdBound: nat)
  decreases k
{
  if k == 0 then n == 0
  else exists i: nat :: i >= 1 &&
    BinToDec(i) <= n && CanDecompose(n - BinToDec(i), k - 1, bdBound)
}

method BinaryDecimal(n: int) returns (result: int)
  requires n > 0
  ensures result >= 1
  ensures CanDecompose(n, result, Pow2(NumDigits(n)))
  ensures forall k | 0 <= k < result :: !CanDecompose(n, k, Pow2(NumDigits(n)))
{
  result := 0;
  var num := n;
  while num > 0 {
    var digit := num % 10;
    if digit > result {
      result := digit;
    }
    num := num / 10;
  }
}
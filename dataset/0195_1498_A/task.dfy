// ===== Specification: models the problem structure =====

ghost function Abs(n: int): nat
{
  if n >= 0 then n else -n
}

// Sum of the base-10 digits of a non-negative integer
ghost function DigitSum(n: int): nat
  requires n >= 0
  decreases n
{
  if n == 0 then 0
  else (n % 10) + DigitSum(n / 10)
}

// Largest d in {1..candidate} that divides both a and b; 0 if none
// Models the mathematical definition: gcd is the LARGEST common divisor
ghost function MaxCommonDivisor(a: int, b: int, candidate: int): nat
  requires a >= 0 && b >= 0 && candidate >= 0
  decreases candidate
{
  if candidate == 0 then 0
  else if a % candidate == 0 && b % candidate == 0 then candidate
  else MaxCommonDivisor(a, b, candidate - 1)
}

// gcd(a, b) = largest positive integer dividing both a and b
// gcd(0, 0) = 0 by convention
ghost function GcdSpec(a: int, b: int): nat
  requires a >= 0 && b >= 0
{
  if a == 0 && b == 0 then 0
  else MaxCommonDivisor(a, b, a + b)
}

// gcdSum(x) = gcd(x, digit_sum(x))
ghost function GcdSumOf(x: int): nat
  requires x >= 0
{
  GcdSpec(x, DigitSum(x))
}

// ===== Methods with specification =====

method Gcd(a: int, b: int) returns (g: int)
  ensures g == GcdSpec(Abs(a), Abs(b))
  decreases *
{
  var x := a;
  var y := b;
  if x < 0 { x := -x; }
  if y < 0 { y := -y; }
  while y != 0
    decreases *
  {
    var temp := y;
    y := x % y;
    x := temp;
  }
  g := x;
}

method GcdSum(n: int) returns (x: int)
  requires n >= 1
  ensures x >= n
  ensures GcdSumOf(x) > 1
  ensures forall y | n <= y < x :: GcdSumOf(y) <= 1
  decreases *
{
  x := n;
  while true
    decreases *
  {
    var digitSum := 0;
    var temp := x;
    if temp < 0 { temp := -temp; }
    while temp > 0
      decreases *
    {
      digitSum := digitSum + (temp % 10);
      temp := temp / 10;
    }
    var g := Gcd(digitSum, x);
    if g > 1 {
      return;
    }
    x := x + 1;
  }
}
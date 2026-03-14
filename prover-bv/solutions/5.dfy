// Problem 5: Euclidean GCD on bitvectors

opaque ghost function Gcd(a: nat, b: nat): nat
  decreases a + b
{
  if a == 0 then b
  else if b == 0 then a
  else if a >= b then Gcd(a - b, b)
  else Gcd(a, b - a)
}

// Lemma: Gcd base cases
lemma GcdZeroLeft(b: nat)
  ensures Gcd(0, b) == b
{
  reveal Gcd();
}

lemma GcdZeroRight(a: nat)
  ensures Gcd(a, 0) == a
{
  reveal Gcd();
}

// Lemma: Gcd step when a >= b > 0
lemma GcdStepA(a: nat, b: nat)
  requires a > 0 && b > 0 && a >= b
  ensures Gcd(a, b) == Gcd(a - b, b)
{
  reveal Gcd();
}

// Lemma: Gcd step when 0 < a < b
lemma GcdStepB(a: nat, b: nat)
  requires a > 0 && b > 0 && b > a
  ensures Gcd(a, b) == Gcd(a, b - a)
{
  reveal Gcd();
}

method EuclidGcd(a0: bv8, b0: bv8) returns (result: bv8)
  requires a0 != 0 || b0 != 0
  ensures result as int == Gcd(a0 as int, b0 as int)
{
  if a0 == 0 {
    GcdZeroLeft(b0 as int);
    return b0;
  }
  if b0 == 0 {
    GcdZeroRight(a0 as int);
    return a0;
  }

  var a: bv8 := a0;
  var b: bv8 := b0;

  while a != 0 && b != 0
    invariant Gcd(a as int, b as int) == Gcd(a0 as int, b0 as int)
    invariant a != 0 || b != 0
    decreases a as int + b as int
  {
    if a >= b {
      GcdStepA(a as int, b as int);
      a := a - b;
    } else {
      GcdStepB(a as int, b as int);
      b := b - a;
    }
  }
  if a == 0 {
    GcdZeroLeft(b as int);
    result := b;
  } else {
    GcdZeroRight(a as int);
    result := a;
  }
}

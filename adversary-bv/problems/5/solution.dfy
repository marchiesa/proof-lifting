// Problem 5: Euclidean GCD on bitvectors - SOLUTION

// Key insight 1: Make Gcd opaque to prevent Z3 from unfolding it uncontrollably.
// Without {:opaque}, Z3 tries to recursively expand Gcd during the loop invariant
// check, leading to resource exhaustion.
ghost function {:opaque} Gcd(a: nat, b: nat): nat
  decreases a + b
{
  if a == 0 then b
  else if b == 0 then a
  else if a >= b then Gcd(a - b, b)
  else Gcd(a, b - a)
}

// Controlled unfolding lemmas: reveal Gcd one step at a time
lemma GcdZeroLeft(b: nat)
  ensures Gcd(0, b) == b
{ reveal Gcd(); }

lemma GcdZeroRight(a: nat)
  ensures Gcd(a, 0) == a
{ reveal Gcd(); }

lemma GcdSubLeft(a: nat, b: nat)
  requires a > 0 && b > 0 && a >= b
  ensures Gcd(a, b) == Gcd(a - b, b)
{ reveal Gcd(); }

lemma GcdSubRight(a: nat, b: nat)
  requires a > 0 && b > 0 && a < b
  ensures Gcd(a, b) == Gcd(a, b - a)
{ reveal Gcd(); }

// Key insight 2: Z3 cannot automatically prove that bv8 subtraction
// (which is modular) matches nat subtraction when there's no underflow.
// This explicit lemma bridges the bitvector and integer theories.
lemma BvSubAsInt(a: bv8, b: bv8)
  requires a >= b
  ensures (a - b) as int == a as int - b as int
{
}

method EuclidGcd(a0: bv8, b0: bv8) returns (result: bv8)
  requires a0 != 0 || b0 != 0
  ensures result as int == Gcd(a0 as int, b0 as int)
{
  if a0 == 0 { GcdZeroLeft(b0 as int); return b0; }
  if b0 == 0 { GcdZeroRight(a0 as int); return a0; }

  var a: bv8 := a0;
  var b: bv8 := b0;

  while a != 0 && b != 0
    invariant Gcd(a as int, b as int) == Gcd(a0 as int, b0 as int)
    decreases a as int + b as int
  {
    if a >= b {
      // Prove bv8 subtraction matches integer subtraction
      BvSubAsInt(a, b);
      // Prove GCD is preserved: Gcd(a, b) == Gcd(a-b, b)
      GcdSubLeft(a as int, b as int);
      a := a - b;
    } else {
      BvSubAsInt(b, a);
      GcdSubRight(a as int, b as int);
      b := b - a;
    }
  }
  // After loop: one of a, b is 0
  if a == 0 {
    GcdZeroLeft(b as int);
    result := b;
  } else {
    GcdZeroRight(a as int);
    result := a;
  }
}

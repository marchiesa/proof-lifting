// Problem 5: Euclidean GCD on bitvectors
//
// Compute the GCD of two bv8 values using repeated subtraction.
// The spec uses a recursive ghost function Gcd on natural numbers,
// and the postcondition bridges bv8 and nat via `as int`.
//
// Z3 struggles because:
// - The GCD spec is recursive on nat, but the implementation uses bv8 arithmetic
// - Theory bridging: Z3 must reason about bv8 subtraction (modular) matching
//   nat subtraction (no overflow), requiring explicit lemmas
// - The loop invariant Gcd(a, b) == Gcd(a0, b0) involves a recursive function
//   that Z3 tends to unfold excessively, causing resource exhaustion
// - The decreases clause a + b requires proving bv8 subtraction decreases
//   the integer sum, which needs bv-to-int conversion reasoning

ghost function Gcd(a: nat, b: nat): nat
  decreases a + b
{
  if a == 0 then b
  else if b == 0 then a
  else if a >= b then Gcd(a - b, b)
  else Gcd(a, b - a)
}

// TASK: Add lemmas, annotations, and loop invariants to make this verify.
// Hint: you may need to make Gcd opaque and control when it unfolds.
method EuclidGcd(a0: bv8, b0: bv8) returns (result: bv8)
  requires a0 != 0 || b0 != 0
  ensures result as int == Gcd(a0 as int, b0 as int)
{
  if a0 == 0 { return b0; }
  if b0 == 0 { return a0; }

  var a: bv8 := a0;
  var b: bv8 := b0;

  while a != 0 && b != 0
    decreases a as int + b as int
  {
    if a >= b {
      a := a - b;
    } else {
      b := b - a;
    }
  }
  if a == 0 {
    result := b;
  } else {
    result := a;
  }
}

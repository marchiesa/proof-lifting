// Problem 4: Non-linear Arithmetic — Power of Two Bound
//
// Task: Add invariants and any needed assertions/lemmas so this method verifies.
// The method computes 2^n iteratively and proves basic properties.

function Pow2(n: nat): nat
{
  if n == 0 then 1 else 2 * Pow2(n - 1)
}

method ComputePow2(n: nat) returns (result: nat)
  ensures result == Pow2(n)
  ensures result >= 1
  ensures n > 0 ==> result % 2 == 0
{
  result := 1;
  var i := 0;
  while i < n
    // TODO: add invariants here
  {
    result := result * 2;
    i := i + 1;
  }
}

// This lemma should be provable but Z3 struggles with it.
// The method multiplies two powers of 2 and proves the result
// is also a power of 2.
method MultiplyPow2(a: nat, b: nat) returns (result: nat)
  ensures result == Pow2(a) * Pow2(b)
  ensures result == Pow2(a + b)
{
  var pa := ComputePow2(a);
  var pb := ComputePow2(b);
  result := pa * pb;
  // TODO: prove result == Pow2(a + b)
}

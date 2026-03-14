// Problem 4: Non-linear Arithmetic — Power of Two Bound (SOLUTION)
//
// The obvious invariant `result == Pow2(i)` is correct and maintains
// through the loop. But Z3 cannot derive properties of Pow2 from
// the recursive definition alone. Specifically:
//
// 1. Z3 can't prove Pow2(n) >= 1 (requires induction)
// 2. Z3 can't prove Pow2(n) % 2 == 0 for n > 0 (requires NL reasoning)
// 3. Z3 can't prove Pow2(a) * Pow2(b) == Pow2(a+b) (requires both induction + NL)
//
// Fix: Provide explicit inductive lemmas for each property.

function Pow2(n: nat): nat
{
  if n == 0 then 1 else 2 * Pow2(n - 1)
}

lemma Pow2Positive(n: nat)
  ensures Pow2(n) >= 1
{
  if n > 0 {
    Pow2Positive(n - 1);
  }
}

lemma Pow2Add(a: nat, b: nat)
  ensures Pow2(a) * Pow2(b) == Pow2(a + b)
{
  if a == 0 {
    assert Pow2(0) == 1;
  } else {
    Pow2Add(a - 1, b);
    // Chain the NL reasoning through linear steps:
    // Pow2(a) * Pow2(b) == (2 * Pow2(a-1)) * Pow2(b)
    //                    == 2 * (Pow2(a-1) * Pow2(b))    [by IH]
    //                    == 2 * Pow2(a-1+b)
    //                    == Pow2(a+b)
    assert Pow2(a) * Pow2(b) == (2 * Pow2(a-1)) * Pow2(b) == 2 * (Pow2(a-1) * Pow2(b));
    assert Pow2(a-1) * Pow2(b) == Pow2(a - 1 + b);
    assert Pow2(a + b) == 2 * Pow2(a + b - 1);
  }
}

lemma Pow2Even(n: nat)
  requires n > 0
  ensures Pow2(n) % 2 == 0
{
  assert Pow2(n) == 2 * Pow2(n-1);
  Pow2Positive(n-1);
}

method ComputePow2(n: nat) returns (result: nat)
  ensures result == Pow2(n)
  ensures result >= 1
  ensures n > 0 ==> result % 2 == 0
{
  result := 1;
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant result == Pow2(i)
  {
    // Tell Z3 how Pow2(i+1) relates to result
    assert Pow2(i + 1) == 2 * Pow2(i);
    result := result * 2;
    i := i + 1;
  }
  // These properties require explicit lemma invocations
  Pow2Positive(n);
  if n > 0 {
    Pow2Even(n);
  }
}

method MultiplyPow2(a: nat, b: nat) returns (result: nat)
  ensures result == Pow2(a) * Pow2(b)
  ensures result == Pow2(a + b)
{
  var pa := ComputePow2(a);
  var pb := ComputePow2(b);
  result := pa * pb;
  // Without this lemma call, Z3 cannot prove the NL identity
  Pow2Add(a, b);
}

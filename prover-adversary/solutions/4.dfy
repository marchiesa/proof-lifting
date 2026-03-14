// Problem 4: Non-linear Arithmetic — Power of Two Bound

function Pow2(n: nat): nat
{
  if n == 0 then 1 else 2 * Pow2(n - 1)
}

lemma Pow2Positive(n: nat)
  ensures Pow2(n) >= 1
{
  if n == 0 {
  } else {
    Pow2Positive(n - 1);
  }
}

lemma Pow2Even(n: nat)
  requires n > 0
  ensures Pow2(n) % 2 == 0
{
  if n == 1 {
    assert Pow2(1) == 2;
  } else {
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
    assert Pow2(a) == 2 * Pow2(a - 1);
    assert Pow2(a) * Pow2(b) == 2 * Pow2(a - 1) * Pow2(b);
    assert 2 * Pow2(a - 1) * Pow2(b) == 2 * (Pow2(a - 1) * Pow2(b));
    assert Pow2(a - 1) * Pow2(b) == Pow2(a - 1 + b);
    assert 2 * Pow2(a - 1 + b) == Pow2(a + b);
  }
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
    result := result * 2;
    i := i + 1;
  }
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
  Pow2Add(a, b);
}

// Compute GCD (Euclidean Algorithm) -- Reference solution with invariants

// Recursive GCD definition
function GcdFunc(a: nat, b: nat): nat
  decreases b
{
  if b == 0 then a
  else GcdFunc(b, a % b)
}

// GCD of positive numbers is positive
lemma GcdPositive(a: nat, b: nat)
  requires a > 0 || b > 0
  ensures GcdFunc(a, b) > 0
  decreases b
{
  if b > 0 {
    assert a % b < b;
    if b > 0 {
      GcdPositive(b, a % b);
    }
  }
}

// GcdFunc(a, 0) == a
lemma GcdBaseCase(a: nat)
  ensures GcdFunc(a, 0) == a
{
}

method Gcd(a: int, b: int) returns (g: int)
  requires a > 0 && b > 0
  ensures g == GcdFunc(a, b)
  ensures g > 0
{
  var x: nat := a;
  var y: nat := b;
  while y != 0
    invariant x >= 0 && y >= 0
    invariant x > 0 || y > 0
    invariant GcdFunc(x, y) == GcdFunc(a, b)
    decreases y
  {
    var temp: nat := y;
    var r: nat := x % y;
    x := temp;
    y := r;
  }
  GcdPositive(a, b);
  g := x;
}

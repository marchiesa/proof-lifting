// Compute GCD (Euclidean Algorithm)
// Task: Add loop invariants so that Dafny can verify this program.

function GcdFunc(a: nat, b: nat): nat
  decreases b
{
  if b == 0 then a
  else GcdFunc(b, a % b)
}

method Gcd(a: int, b: int) returns (g: int)
  requires a > 0 && b > 0
  ensures g == GcdFunc(a, b)
  ensures g > 0
{
  var x: nat := a;
  var y: nat := b;
  while y != 0
  {
    var temp: nat := y;
    var r: nat := x % y;
    x := temp;
    y := r;
  }
  g := x;
}

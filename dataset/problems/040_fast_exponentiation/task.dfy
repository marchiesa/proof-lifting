// Fast Exponentiation (Exponentiation by Squaring)
// Task: Add loop invariants so that Dafny can verify this program.

function Power(base: int, exp: nat): int
{
  if exp == 0 then 1
  else base * Power(base, exp - 1)
}

method FastPow(base: int, exp: nat) returns (result: int)
  ensures result == Power(base, exp)
{
  result := 1;
  var b := base;
  var e := exp;
  while e > 0
  {
    if e % 2 == 1 {
      result := result * b;
    }
    b := b * b;
    e := e / 2;
  }
}

// Fast Exponentiation -- Test cases

function Power(base: int, exp: nat): int
{
  if exp == 0 then 1
  else base * Power(base, exp - 1)
}

method {:axiom} FastPow(base: int, exp: nat) returns (result: int)
  ensures result == Power(base, exp)

method TestPow2_10()
{
  var r := FastPow(2, 10);
  assert Power(2, 10) == 2 * Power(2, 9);
  // We can verify via the spec
  assert r == Power(2, 10);
}

method TestPow0()
{
  var r := FastPow(5, 0);
  assert Power(5, 0) == 1;
  assert r == 1;
}

method TestPow1()
{
  var r := FastPow(7, 1);
  assert Power(7, 1) == 7 * Power(7, 0) == 7;
  assert r == 7;
}

method TestPowNegBase()
{
  var r := FastPow(-2, 3);
  assert Power(-2, 3) == -2 * Power(-2, 2);
  assert Power(-2, 2) == -2 * Power(-2, 1);
  assert Power(-2, 1) == -2 * Power(-2, 0) == -2;
  assert r == -8;
}

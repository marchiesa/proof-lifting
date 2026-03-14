// Integer Square Root -- Test cases

method {:axiom} IntSqrt(n: nat) returns (r: nat)
  ensures r * r <= n
  ensures (r + 1) * (r + 1) > n

method TestZero()
{
  var r := IntSqrt(0);
  assert r * r <= 0;
  assert r == 0;
}

method TestOne()
{
  var r := IntSqrt(1);
  assert r * r <= 1;
  assert (r + 1) * (r + 1) > 1;
}

method TestPerfectSquare()
{
  var r := IntSqrt(9);
  assert r * r <= 9;
  assert (r + 1) * (r + 1) > 9;
}

method TestNonPerfectSquare()
{
  var r := IntSqrt(8);
  assert r * r <= 8;
  assert (r + 1) * (r + 1) > 8;
}

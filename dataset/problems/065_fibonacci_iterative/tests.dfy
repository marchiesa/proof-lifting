// Fibonacci -- Test cases

function Fib(n: nat): nat
{
  if n == 0 then 0
  else if n == 1 then 1
  else Fib(n - 1) + Fib(n - 2)
}

method {:axiom} ComputeFib(n: nat) returns (r: nat)
  ensures r == Fib(n)

method TestFibZero()
{
  var r := ComputeFib(0);
  assert r == 0;
}

method TestFibOne()
{
  var r := ComputeFib(1);
  assert r == 1;
}

method TestFibFive()
{
  var r := ComputeFib(5);
  assert Fib(5) == 5;
  assert r == 5;
}

method TestFibTen()
{
  var r := ComputeFib(10);
  assert Fib(10) == 55;
  assert r == 55;
}

// Fibonacci (Iterative) -- Runtime spec tests

// Copy spec function from task.dfy
function Fib(n: nat): nat
{
  if n == 0 then 0
  else if n == 1 then 1
  else Fib(n - 1) + Fib(n - 2)
}

method Main()
{
  // Test Fib function directly on known values
  expect Fib(0) == 0, "Fib(0) should be 0";
  expect Fib(1) == 1, "Fib(1) should be 1";
  expect Fib(2) == 1, "Fib(2) should be 1";
  expect Fib(3) == 2, "Fib(3) should be 2";
  expect Fib(4) == 3, "Fib(4) should be 3";
  expect Fib(5) == 5, "Fib(5) should be 5";
  expect Fib(6) == 8, "Fib(6) should be 8";
  expect Fib(7) == 13, "Fib(7) should be 13";
  expect Fib(10) == 55, "Fib(10) should be 55";

  // Negative: wrong values
  expect Fib(5) != 4, "Fib(5) should not be 4";
  expect Fib(5) != 6, "Fib(5) should not be 6";
  expect Fib(0) != 1, "Fib(0) should not be 1";
  expect Fib(10) != 54, "Fib(10) should not be 54";

  // Test the recurrence relation itself
  var i := 2;
  while i <= 15
  {
    expect Fib(i) == Fib(i - 1) + Fib(i - 2), "Fib recurrence should hold";
    i := i + 1;
  }

  print "All spec tests passed\n";
}

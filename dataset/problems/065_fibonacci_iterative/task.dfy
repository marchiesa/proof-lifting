// Fibonacci (Iterative)
// Task: Add loop invariants so that Dafny can verify this program.

function Fib(n: nat): nat
{
  if n == 0 then 0
  else if n == 1 then 1
  else Fib(n - 1) + Fib(n - 2)
}

method ComputeFib(n: nat) returns (r: nat)
  ensures r == Fib(n)
{
  if n == 0 { return 0; }
  var prev := 0;
  var curr := 1;
  var i := 1;
  while i < n
  {
    var next := prev + curr;
    prev := curr;
    curr := next;
    i := i + 1;
  }
  return curr;
}

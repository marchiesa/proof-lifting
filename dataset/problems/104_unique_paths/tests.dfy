// Unique Paths -- Test cases

function Paths(m: nat, n: nat): nat
  decreases m + n
{
  if m == 0 || n == 0 then 0
  else if m == 1 || n == 1 then 1
  else Paths(m - 1, n) + Paths(m, n - 1)
}

method {:axiom} UniquePaths(m: nat, n: nat) returns (result: nat)
  requires m > 0 && n > 0
  ensures result == Paths(m, n)

method Test1x1() { var r := UniquePaths(1, 1); assert r == 1; }
method Test2x2() { var r := UniquePaths(2, 2); }
method Test3x3() { var r := UniquePaths(3, 3); }

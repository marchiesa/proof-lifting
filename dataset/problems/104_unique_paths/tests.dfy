// Unique Paths -- Runtime spec tests

function Paths(m: nat, n: nat): nat
  decreases m + n
{
  if m == 0 || n == 0 then 0
  else if m == 1 || n == 1 then 1
  else Paths(m - 1, n) + Paths(m, n - 1)
}

method Main()
{
  // Paths: base cases
  expect Paths(0, 0) == 0, "Paths(0,0) = 0";
  expect Paths(0, 5) == 0, "Paths(0,5) = 0";
  expect Paths(5, 0) == 0, "Paths(5,0) = 0";
  expect Paths(1, 1) == 1, "Paths(1,1) = 1";
  expect Paths(1, 5) == 1, "Paths(1,5) = 1";
  expect Paths(5, 1) == 1, "Paths(5,1) = 1";

  // Paths: known values
  expect Paths(2, 2) == 2, "Paths(2,2) = 2";
  expect Paths(3, 3) == 6, "Paths(3,3) = 6";
  expect Paths(3, 2) == 3, "Paths(3,2) = 3";
  expect Paths(2, 3) == 3, "Paths(2,3) = 3";
  expect Paths(4, 4) == 20, "Paths(4,4) = 20";

  // Paths: symmetry
  expect Paths(3, 7) == Paths(7, 3), "Paths(3,7) == Paths(7,3)";

  // Paths: negative tests
  expect Paths(2, 2) != 1, "Paths(2,2) != 1";
  expect Paths(3, 3) != 4, "Paths(3,3) != 4";

  // Paths: recursive property
  expect Paths(3, 3) == Paths(2, 3) + Paths(3, 2), "Paths(3,3) = Paths(2,3) + Paths(3,2)";

  print "All spec tests passed\n";
}

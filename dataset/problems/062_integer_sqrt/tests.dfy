// Integer Square Root -- Runtime spec tests

// The spec is the postcondition: r * r <= n && (r + 1) * (r + 1) > n
// We test these properties directly on known values.

method CheckIntSqrtSpec(n: nat, r: nat) returns (ok: bool)
{
  ok := r * r <= n && (r + 1) * (r + 1) > n;
}

method Main()
{
  // Positive tests: correct square roots
  var r := CheckIntSqrtSpec(0, 0);
  expect r, "sqrt(0) = 0";

  r := CheckIntSqrtSpec(1, 1);
  expect r, "sqrt(1) = 1";

  r := CheckIntSqrtSpec(4, 2);
  expect r, "sqrt(4) = 2";

  r := CheckIntSqrtSpec(8, 2);
  expect r, "sqrt(8) = 2";

  r := CheckIntSqrtSpec(9, 3);
  expect r, "sqrt(9) = 3";

  r := CheckIntSqrtSpec(15, 3);
  expect r, "sqrt(15) = 3";

  r := CheckIntSqrtSpec(16, 4);
  expect r, "sqrt(16) = 4";

  r := CheckIntSqrtSpec(100, 10);
  expect r, "sqrt(100) = 10";

  r := CheckIntSqrtSpec(2, 1);
  expect r, "sqrt(2) = 1";

  // Negative tests: wrong square roots
  r := CheckIntSqrtSpec(4, 1);
  expect !r, "sqrt(4) != 1";

  r := CheckIntSqrtSpec(4, 3);
  expect !r, "sqrt(4) != 3";

  r := CheckIntSqrtSpec(9, 2);
  expect !r, "sqrt(9) != 2";

  r := CheckIntSqrtSpec(9, 4);
  expect !r, "sqrt(9) != 4";

  r := CheckIntSqrtSpec(0, 1);
  expect !r, "sqrt(0) != 1";

  print "All spec tests passed\n";
}

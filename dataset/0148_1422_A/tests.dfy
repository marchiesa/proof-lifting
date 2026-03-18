predicate QuadrilateralInequality(a: int, b: int, c: int, d: int)
{
  a < b + c + d &&
  b < a + c + d &&
  c < a + b + d &&
  d < a + b + c
}

predicate CanFormQuadrilateral(a: int, b: int, c: int, d: int)
{
  a > 0 && b > 0 && c > 0 && d > 0 &&
  QuadrilateralInequality(a, b, c, d)
}

method Fence(a: int, b: int, c: int) returns (d: int)
  requires a > 0 && b > 0 && c > 0
  ensures d > 0
  ensures CanFormQuadrilateral(a, b, c, d)
{
  d := a + b + c - 1;
}

method Main()
{
  // === SPEC POSITIVE tests ===
  expect CanFormQuadrilateral(1, 2, 3, 5), "spec positive 1a";
  expect CanFormQuadrilateral(12, 34, 56, 101), "spec positive 1b";
  expect CanFormQuadrilateral(2434, 2442, 14, 4889), "spec positive 2";
  expect CanFormQuadrilateral(10, 20, 10, 39), "spec positive 3";
  expect CanFormQuadrilateral(3, 4, 5, 11), "spec positive 4";
  expect CanFormQuadrilateral(2, 1, 2, 4), "spec positive 5";
  expect CanFormQuadrilateral(5, 4, 3, 11), "spec positive 6";

  // === SPEC NEGATIVE tests ===
  expect !CanFormQuadrilateral(1, 2, 3, 6), "spec negative 1";
  expect !CanFormQuadrilateral(2434, 2442, 14, 4890), "spec negative 2";
  expect !CanFormQuadrilateral(10, 20, 10, 40), "spec negative 3";
  expect !CanFormQuadrilateral(3, 4, 5, 12), "spec negative 4";
  expect !CanFormQuadrilateral(2, 1, 2, 5), "spec negative 5";
  expect !CanFormQuadrilateral(5, 4, 3, 12), "spec negative 6";

  // === IMPLEMENTATION tests ===
  var d1 := Fence(1, 2, 3);
  expect d1 == 5, "impl test 1a failed";

  var d2 := Fence(12, 34, 56);
  expect d2 == 101, "impl test 1b failed";

  var d3 := Fence(2434, 2442, 14);
  expect d3 == 4889, "impl test 2 failed";

  var d4 := Fence(10, 20, 10);
  expect d4 == 39, "impl test 3 failed";

  var d5 := Fence(3, 4, 5);
  expect d5 == 11, "impl test 4 failed";

  var d6 := Fence(2, 1, 2);
  expect d6 == 4, "impl test 5 failed";

  var d7 := Fence(5, 4, 3);
  expect d7 == 11, "impl test 6 failed";

  print "All tests passed\n";
}
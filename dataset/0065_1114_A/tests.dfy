predicate ValidAllocation(x: int, y: int, z: int, a: int, b: int, c: int,
                          ga: int, gd: int, pd: int, gm: int, pm: int, bm: int)
{
  ga >= 0 && gd >= 0 && pd >= 0 && gm >= 0 && pm >= 0 && bm >= 0 &&
  ga >= x &&
  gd + pd >= y &&
  gm + pm + bm >= z &&
  ga + gd + gm <= a &&
  pd + pm <= b &&
  bm <= c
}

predicate Feasible(x: int, y: int, z: int, a: int, b: int, c: int)
  requires x >= 0 && y >= 0 && z >= 0 && a >= 0 && b >= 0 && c >= 0
{
  var bound := if a - x < y then a - x else y;
  exists gd: int | 0 <= gd <= bound ::
    ValidAllocation(x, y, z, a, b, c,
                    x, gd, y - gd, a - x - gd, b - (y - gd), c)
}

method GotAnyGrapes(x: int, y: int, z: int, a: int, b: int, c: int) returns (result: bool)
  requires x >= 0 && y >= 0 && z >= 0 && a >= 0 && b >= 0 && c >= 0
  ensures result == Feasible(x, y, z, a, b, c)
{
  var a' := a;
  var b' := b;
  var c' := c;

  c' := c' - z;
  if c' < 0 {
    b' := b' + c';
  }
  b' := b' - y;
  if b' < 0 {
    a' := a' + b';
  }
  a' := a' - x;

  result := a' >= 0;
}

method Main()
{
  var r: bool;

  // === SPEC POSITIVE TESTS ===
  // (Feasible with correct expected output — quantifier bound is ≤4 for all cases)
  expect Feasible(1, 6, 2, 4, 3, 3) == true,   "spec positive 1";
  expect Feasible(5, 1, 1, 4, 3, 2) == false,   "spec positive 2";
  expect Feasible(1, 1, 100000, 4, 2, 99995) == false, "spec positive 3";
  expect Feasible(1, 2, 3, 3, 2, 1) == true,    "spec positive 4";
  expect Feasible(1, 8, 4, 3, 1, 9) == false,   "spec positive 5";
  expect Feasible(6, 1, 2, 4, 9, 6) == false,   "spec positive 6";
  expect Feasible(100000, 100000, 100000, 100000, 100000, 100000) == true, "spec positive 7";
  expect Feasible(3, 2, 1, 1, 2, 3) == false,   "spec positive 8";
  expect Feasible(99999, 99998, 99997, 99997, 99998, 99999) == false, "spec positive 9";
  expect Feasible(1, 7, 9, 4, 5, 7) == false,   "spec positive 10";

  // === SPEC NEGATIVE TESTS ===
  // (Feasible must disagree with the wrong output)
  expect Feasible(1, 6, 2, 4, 3, 3) != false,   "spec negative 1";
  expect Feasible(5, 1, 1, 4, 3, 2) != true,    "spec negative 2";
  expect Feasible(1, 1, 100000, 4, 2, 99995) != true, "spec negative 3";
  expect Feasible(1, 2, 3, 3, 2, 1) != false,   "spec negative 4";
  expect Feasible(1, 8, 4, 3, 1, 9) != true,    "spec negative 5";
  expect Feasible(6, 1, 2, 4, 9, 6) != true,    "spec negative 6";
  expect Feasible(100000, 100000, 100000, 100000, 100000, 100000) != false, "spec negative 7";
  expect Feasible(3, 2, 1, 1, 2, 3) != true,    "spec negative 8";
  expect Feasible(99999, 99998, 99997, 99997, 99998, 99999) != true, "spec negative 9";
  expect Feasible(1, 7, 9, 4, 5, 7) != true,    "spec negative 10";

  // === IMPLEMENTATION TESTS ===
  r := GotAnyGrapes(1, 6, 2, 4, 3, 3);
  expect r == true, "impl test 1 failed";

  r := GotAnyGrapes(5, 1, 1, 4, 3, 2);
  expect r == false, "impl test 2 failed";

  r := GotAnyGrapes(1, 1, 100000, 4, 2, 99995);
  expect r == false, "impl test 3 failed";

  r := GotAnyGrapes(1, 2, 3, 3, 2, 1);
  expect r == true, "impl test 4 failed";

  r := GotAnyGrapes(1, 8, 4, 3, 1, 9);
  expect r == false, "impl test 5 failed";

  r := GotAnyGrapes(6, 1, 2, 4, 9, 6);
  expect r == false, "impl test 6 failed";

  r := GotAnyGrapes(100000, 100000, 100000, 100000, 100000, 100000);
  expect r == true, "impl test 7 failed";

  r := GotAnyGrapes(3, 2, 1, 1, 2, 3);
  expect r == false, "impl test 8 failed";

  r := GotAnyGrapes(99999, 99998, 99997, 99997, 99998, 99999);
  expect r == false, "impl test 9 failed";

  r := GotAnyGrapes(1, 7, 9, 4, 5, 7);
  expect r == false, "impl test 10 failed";

  r := GotAnyGrapes(99999, 100000, 100000, 100000, 100000, 100000);
  expect r == true, "impl test 11 failed";

  r := GotAnyGrapes(100000, 99999, 100000, 100000, 100000, 100000);
  expect r == true, "impl test 12 failed";

  r := GotAnyGrapes(100000, 100000, 99999, 100000, 100000, 100000);
  expect r == true, "impl test 13 failed";

  r := GotAnyGrapes(100000, 100000, 100000, 99999, 100000, 100000);
  expect r == false, "impl test 14 failed";

  r := GotAnyGrapes(100000, 100000, 100000, 100000, 99999, 100000);
  expect r == false, "impl test 15 failed";

  r := GotAnyGrapes(100000, 100000, 100000, 100000, 100000, 99999);
  expect r == false, "impl test 16 failed";

  r := GotAnyGrapes(4, 6, 4, 4, 5, 6);
  expect r == false, "impl test 17 failed";

  r := GotAnyGrapes(6, 1, 9, 1, 7, 8);
  expect r == false, "impl test 18 failed";

  r := GotAnyGrapes(4, 10, 5, 4, 10, 5);
  expect r == true, "impl test 19 failed";

  r := GotAnyGrapes(10, 1, 7, 1, 9, 10);
  expect r == false, "impl test 20 failed";

  print "All tests passed\n";
}
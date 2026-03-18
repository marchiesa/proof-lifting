predicate ValidPair(a: int, b: int, x: int)
{
  1 <= a <= x &&
  1 <= b <= x &&
  a % b == 0 &&
  a * b > x &&
  a / b < x
}

predicate SolutionExists(x: int)
{
  exists a | 1 <= a <= x :: exists b | 1 <= b <= x :: ValidPair(a, b, x)
}

method EhabConstruction(x: int) returns (a: int, b: int, found: bool)
  ensures found ==> ValidPair(a, b, x)
  ensures !found ==> !SolutionExists(x)
{
  a := 0;
  b := 0;
  found := false;

  var ai := 1;
  while ai <= x && !found
  {
    var bi := 1;
    while bi <= ai && !found
    {
      if ai % bi == 0 && ai * bi > x && ai / bi < x {
        a := ai;
        b := bi;
        found := true;
      }
      bi := bi + 1;
    }
    ai := ai + 1;
  }
}

method Main()
{
  var a: int, b: int, found: bool;

  // === SPEC POSITIVE TESTS ===
  // found ==> ValidPair(a, b, x) with correct outputs
  expect ValidPair(4, 4, 10),  "spec positive 1";   // x=10
  expect ValidPair(3, 3, 5),   "spec positive 3";   // x=5
  expect ValidPair(3, 3, 8),   "spec positive 4";   // x=8
  expect ValidPair(5, 5, 20),  "spec positive 5";   // x=20
  expect ValidPair(8, 8, 55),  "spec positive 6";   // x=55
  expect ValidPair(9, 9, 78),  "spec positive 7";   // x=78
  expect ValidPair(10, 10, 89),"spec positive 8";   // x=89
  expect ValidPair(11, 11, 100),"spec positive 9";  // x=100
  expect ValidPair(2, 2, 2),   "spec positive 10";  // x=2
  // !found ==> !SolutionExists(x)
  expect !SolutionExists(1),   "spec positive 2";   // x=1, no solution

  // === SPEC NEGATIVE TESTS ===
  // Wrong outputs must NOT satisfy ValidPair
  expect !ValidPair(5, 4, 10),   "spec negative 1";  // x=10, wrong: 5 4 (5%4!=0)
  expect !ValidPair(4, 3, 5),    "spec negative 3";  // x=5,  wrong: 4 3 (4%3!=0)
  expect !ValidPair(4, 3, 8),    "spec negative 4";  // x=8,  wrong: 4 3 (4%3!=0)
  expect !ValidPair(6, 5, 20),   "spec negative 5";  // x=20, wrong: 6 5 (6%5!=0)
  expect !ValidPair(9, 8, 55),   "spec negative 6";  // x=55, wrong: 9 8 (9%8!=0)
  expect !ValidPair(10, 9, 78),  "spec negative 7";  // x=78, wrong: 10 9 (10%9!=0)
  expect !ValidPair(11, 10, 89), "spec negative 8";  // x=89, wrong: 11 10 (11%10!=0)
  expect !ValidPair(12, 11, 100),"spec negative 9";  // x=100,wrong: 12 11 (12%11!=0)
  expect !ValidPair(3, 2, 2),    "spec negative 10"; // x=2,  wrong: 3 2 (3>x)

  // === IMPLEMENTATION TESTS ===
  a, b, found := EhabConstruction(10);
  expect found && a == 4 && b == 4, "impl test 1 failed";

  a, b, found := EhabConstruction(1);
  expect !found, "impl test 2 failed";

  a, b, found := EhabConstruction(5);
  expect found && a == 3 && b == 3, "impl test 3 failed";

  a, b, found := EhabConstruction(8);
  expect found && a == 3 && b == 3, "impl test 4 failed";

  a, b, found := EhabConstruction(20);
  expect found && a == 5 && b == 5, "impl test 5 failed";

  a, b, found := EhabConstruction(55);
  expect found && a == 8 && b == 8, "impl test 6 failed";

  a, b, found := EhabConstruction(78);
  expect found && a == 9 && b == 9, "impl test 7 failed";

  a, b, found := EhabConstruction(89);
  expect found && a == 10 && b == 10, "impl test 8 failed";

  a, b, found := EhabConstruction(100);
  expect found && a == 11 && b == 11, "impl test 9 failed";

  a, b, found := EhabConstruction(2);
  expect found && a == 2 && b == 2, "impl test 10 failed";

  print "All tests passed\n";
}
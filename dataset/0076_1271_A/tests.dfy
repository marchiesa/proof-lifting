// --- Specification functions/predicates ---

function MinVal(x: int, y: int): int {
  if x <= y then x else y
}

function MaxVal(x: int, y: int): int {
  if x >= y then x else y
}

predicate ValidAllocation(a: int, b: int, c: int, d: int, x: int, y: int) {
  x >= 0 && y >= 0 &&
  x <= a &&
  y <= b &&
  y <= c &&
  x + y <= d
}

function AllocationCost(x: int, y: int, e: int, f: int): int {
  x * e + y * f
}

function BestY(b: int, c: int, d: int, f: int, x: int): int
  requires 0 <= b && 0 <= c && 0 <= x <= d
{
  var maxY := MinVal(b, MinVal(c, d - x));
  if f >= 0 then maxY else 0
}

function CostForX(b: int, c: int, d: int, e: int, f: int, x: int): int
  requires 0 <= b && 0 <= c && 0 <= x <= d
{
  AllocationCost(x, BestY(b, c, d, f, x), e, f)
}

function MaxCostRange(b: int, c: int, d: int, e: int, f: int, lo: int, hi: int): int
  requires 0 <= b && 0 <= c && 0 <= d
  requires 0 <= lo <= hi <= d
  decreases hi - lo
{
  if lo == hi then
    CostForX(b, c, d, e, f, lo)
  else
    var mid := lo + (hi - lo) / 2;
    MaxVal(
      MaxCostRange(b, c, d, e, f, lo, mid),
      MaxCostRange(b, c, d, e, f, mid + 1, hi)
    )
}

function OptimalSuitsCost(a: int, b: int, c: int, d: int, e: int, f: int): int
  requires 0 <= a && 0 <= b && 0 <= c && 0 <= d
{
  MaxCostRange(b, c, d, e, f, 0, MinVal(a, d))
}

// Combined predicate matching all three ensures clauses of Suits
predicate SuitsSpec(a: int, b: int, c: int, d: int, e: int, f: int, maxCost: int)
  requires 0 <= a && 0 <= b && 0 <= c && 0 <= d
{
  // Achievability
  (exists x: int | 0 <= x <= MinVal(a, d) ::
    ValidAllocation(a, b, c, d, x, BestY(b, c, d, f, x)) &&
    AllocationCost(x, BestY(b, c, d, f, x), e, f) == maxCost) &&
  // Optimality
  (forall x: int | 0 <= x <= MinVal(a, d) ::
    CostForX(b, c, d, e, f, x) <= maxCost) &&
  // Computed optimum
  maxCost == OptimalSuitsCost(a, b, c, d, e, f)
}

// --- Implementation ---

method Min2(x: int, y: int) returns (m: int)
  ensures m == MinVal(x, y)
{
  if x < y { m := x; } else { m := y; }
}

method Min3(x: int, y: int, z: int) returns (m: int)
  ensures m == MinVal(x, MinVal(y, z))
{
  m := x;
  if y < m { m := y; }
  if z < m { m := z; }
}

method Suits(a: int, b: int, c: int, d: int, e: int, f: int) returns (maxCost: int)
  requires 0 <= a && 0 <= b && 0 <= c && 0 <= d
  requires 0 <= e && 0 <= f
  ensures exists x: int | 0 <= x <= MinVal(a, d) ::
    ValidAllocation(a, b, c, d, x, BestY(b, c, d, f, x)) &&
    AllocationCost(x, BestY(b, c, d, f, x), e, f) == maxCost
  ensures forall x: int | 0 <= x <= MinVal(a, d) ::
    CostForX(b, c, d, e, f, x) <= maxCost
  ensures maxCost == OptimalSuitsCost(a, b, c, d, e, f)
{
  if e > f {
    var x := Min2(a, d);
    var newD := d - x;
    var m := Min3(b, c, newD);
    maxCost := x * e + m * f;
  } else {
    var x := Min3(b, c, d);
    var newD := d - x;
    var m := Min2(a, newD);
    maxCost := x * f + m * e;
  }
}

method Main()
{
  var result: int;

  // === SPEC POSITIVE TESTS (small inputs, bounded quantifiers are fast) ===
  // Test 1: (4,5,6,3,1,2) -> 6, MinVal(a,d)=3
  expect SuitsSpec(4, 5, 6, 3, 1, 2, 6), "spec positive 1";
  // Test 2: (12,11,13,20,4,6) -> 102, MinVal(a,d)=12
  expect SuitsSpec(12, 11, 13, 20, 4, 6, 102), "spec positive 2";
  // Test 3: (17,14,5,21,15,17) -> 325, MinVal(a,d)=17
  expect SuitsSpec(17, 14, 5, 21, 15, 17, 325), "spec positive 3";
  // Test 12: (1,1,1,2,100,200) -> 300, MinVal(a,d)=1
  expect SuitsSpec(1, 1, 1, 2, 100, 200, 300), "spec positive 4";
  // Custom: (0,0,0,0,5,3) -> 0, MinVal(a,d)=0
  expect SuitsSpec(0, 0, 0, 0, 5, 3, 0), "spec positive 5";
  // Custom: (2,2,2,3,1,2) -> 5, MinVal(a,d)=2
  expect SuitsSpec(2, 2, 2, 3, 1, 2, 5), "spec positive 6";
  // Custom: (3,1,2,5,4,3) -> 15, MinVal(a,d)=3
  expect SuitsSpec(3, 1, 2, 5, 4, 3, 15), "spec positive 7";

  // === SPEC NEGATIVE TESTS (small inputs, wrong outputs rejected) ===
  // Neg 1: (4,5,6,3,1,2) -> wrong 7 (correct 6)
  expect !SuitsSpec(4, 5, 6, 3, 1, 2, 7), "spec negative 1";
  // Neg 2: (12,11,13,20,4,6) -> wrong 103 (correct 102)
  expect !SuitsSpec(12, 11, 13, 20, 4, 6, 103), "spec negative 2";
  // Neg 3: (17,14,5,21,15,17) -> wrong 326 (correct 325)
  expect !SuitsSpec(17, 14, 5, 21, 15, 17, 326), "spec negative 3";
  // Custom neg: (1,1,1,2,100,200) -> wrong 301 (correct 300)
  expect !SuitsSpec(1, 1, 1, 2, 100, 200, 301), "spec negative 4";
  // Custom neg: (0,0,0,0,5,3) -> wrong 1 (correct 0)
  expect !SuitsSpec(0, 0, 0, 0, 5, 3, 1), "spec negative 5";
  // Custom neg: (2,2,2,3,1,2) -> wrong 6 (correct 5)
  expect !SuitsSpec(2, 2, 2, 3, 1, 2, 6), "spec negative 6";
  // Custom neg: (3,1,2,5,4,3) -> wrong 16 (correct 15)
  expect !SuitsSpec(3, 1, 2, 5, 4, 3, 16), "spec negative 7";

  // === IMPLEMENTATION TESTS (all 20 test pairs) ===
  result := Suits(4, 5, 6, 3, 1, 2);
  expect result == 6, "impl test 1 failed";

  result := Suits(12, 11, 13, 20, 4, 6);
  expect result == 102, "impl test 2 failed";

  result := Suits(17, 14, 5, 21, 15, 17);
  expect result == 325, "impl test 3 failed";

  result := Suits(43475, 48103, 50473, 97918, 991, 974);
  expect result == 89936047, "impl test 4 failed";

  result := Suits(35361, 35182, 68078, 30077, 870, 907);
  expect result == 27279839, "impl test 5 failed";

  result := Suits(84205, 15736, 30259, 79331, 647, 378);
  expect result == 51327157, "impl test 6 failed";

  result := Suits(220, 623, 94, 463, 28, 656);
  expect result == 67824, "impl test 7 failed";

  result := Suits(100000, 100000, 100000, 100000, 1000, 1);
  expect result == 100000000, "impl test 8 failed";

  result := Suits(22606, 4759, 37264, 19105, 787, 237);
  expect result == 15035635, "impl test 9 failed";

  result := Suits(630, 312, 279, 823, 316, 915);
  expect result == 427189, "impl test 10 failed";

  result := Suits(86516, 30436, 14408, 80824, 605, 220);
  expect result == 48898520, "impl test 11 failed";

  result := Suits(1, 1, 1, 2, 100, 200);
  expect result == 300, "impl test 12 failed";

  result := Suits(406, 847, 512, 65, 86, 990);
  expect result == 64350, "impl test 13 failed";

  result := Suits(250, 400, 766, 246, 863, 166);
  expect result == 212298, "impl test 14 failed";

  result := Suits(724, 20, 391, 850, 639, 149);
  expect result == 465616, "impl test 15 failed";

  result := Suits(30233, 27784, 36393, 81065, 782, 953);
  expect result == 50120358, "impl test 16 failed";

  result := Suits(61455, 43924, 94322, 83903, 855, 232);
  expect result == 57751961, "impl test 17 failed";

  result := Suits(68576, 46084, 31772, 10708, 632, 408);
  expect result == 6767456, "impl test 18 failed";

  result := Suits(19969, 99297, 44283, 67490, 71, 20);
  expect result == 2303459, "impl test 19 failed";

  result := Suits(68814, 96071, 14437, 59848, 848, 195);
  expect result == 50751104, "impl test 20 failed";

  print "All tests passed\n";
}
// === Formal Specification ===

function FloorDistance(a: int, b: int): int
{
  if a >= b then a - b else b - a
}

function StairsTime(x: int, y: int, t1: int): int
{
  t1 * FloorDistance(x, y)
}

function ElevatorApproachTime(z: int, x: int, t2: int): int
{
  t2 * FloorDistance(z, x)
}

function ElevatorRideTime(x: int, y: int, t2: int): int
{
  t2 * FloorDistance(x, y)
}

function DoorOpsTime(t3: int): int
{
  3 * t3
}

function ElevatorTotalTime(x: int, y: int, z: int, t2: int, t3: int): int
{
  ElevatorApproachTime(z, x, t2) + ElevatorRideTime(x, y, t2) + DoorOpsTime(t3)
}

predicate ShouldUseElevator(x: int, y: int, z: int, t1: int, t2: int, t3: int)
{
  StairsTime(x, y, t1) >= ElevatorTotalTime(x, y, z, t2, t3)
}

// Combined ensures predicate: encapsulates both ensures clauses
predicate EnsuresHolds(x: int, y: int, z: int, t1: int, t2: int, t3: int, result: string)
{
  (result == "YES" <==> ShouldUseElevator(x, y, z, t1, t2, t3)) &&
  (result == "YES" || result == "NO")
}

// === Method with specification ===

method ElevatorOrStairs(x: int, y: int, z: int, t1: int, t2: int, t3: int) returns (result: string)
  requires x >= 1 && y >= 1 && z >= 1
  requires x != y
  requires t1 >= 1 && t2 >= 1 && t3 >= 1
  ensures result == "YES" <==> ShouldUseElevator(x, y, z, t1, t2, t3)
  ensures result == "YES" || result == "NO"
{
  var dxy := if x >= y then x - y else y - x;
  var dxz := if x >= z then x - z else z - x;
  if t1 * dxy >= t2 * dxy + t2 * dxz + t3 * 3 {
    result := "YES";
  } else {
    result := "NO";
  }
}

method Main()
{
  // === SPEC POSITIVE tests ===
  // Correct output satisfies both ensures clauses
  expect EnsuresHolds(5, 1, 4, 4, 2, 1, "YES"), "spec positive 1";
  expect EnsuresHolds(1, 6, 6, 2, 1, 1, "NO"), "spec positive 2";
  expect EnsuresHolds(4, 1, 7, 4, 1, 2, "YES"), "spec positive 3";
  expect EnsuresHolds(749, 864, 931, 266, 94, 891, "NO"), "spec positive 4";
  expect EnsuresHolds(719, 137, 307, 244, 724, 777, "NO"), "spec positive 5";
  expect EnsuresHolds(608, 11, 980, 338, 208, 78, "YES"), "spec positive 6";
  expect EnsuresHolds(571, 695, 153, 288, 64, 421, "NO"), "spec positive 7";
  expect EnsuresHolds(837, 544, 703, 808, 549, 694, "YES"), "spec positive 8";
  expect EnsuresHolds(271, 634, 606, 95, 39, 523, "YES"), "spec positive 9";
  expect EnsuresHolds(1000, 999, 1000, 1000, 1000, 1000, "NO"), "spec positive 10";

  // === SPEC NEGATIVE tests ===
  // Wrong output (wrong casing) must be rejected by the ensures clauses
  expect !EnsuresHolds(5, 1, 4, 4, 2, 1, "No"), "spec negative 1";
  expect !EnsuresHolds(1, 6, 6, 2, 1, 1, "Yes"), "spec negative 2";
  expect !EnsuresHolds(4, 1, 7, 4, 1, 2, "No"), "spec negative 3";
  expect !EnsuresHolds(749, 864, 931, 266, 94, 891, "Yes"), "spec negative 4";
  expect !EnsuresHolds(719, 137, 307, 244, 724, 777, "Yes"), "spec negative 5";
  expect !EnsuresHolds(608, 11, 980, 338, 208, 78, "No"), "spec negative 6";
  expect !EnsuresHolds(571, 695, 153, 288, 64, 421, "Yes"), "spec negative 7";
  expect !EnsuresHolds(837, 544, 703, 808, 549, 694, "No"), "spec negative 8";
  expect !EnsuresHolds(271, 634, 606, 95, 39, 523, "No"), "spec negative 9";
  expect !EnsuresHolds(1000, 999, 1000, 1000, 1000, 1000, "Yes"), "spec negative 10";

  // === IMPLEMENTATION tests ===
  var r: string;

  r := ElevatorOrStairs(5, 1, 4, 4, 2, 1);
  expect r == "YES", "impl test 1 failed";

  r := ElevatorOrStairs(1, 6, 6, 2, 1, 1);
  expect r == "NO", "impl test 2 failed";

  r := ElevatorOrStairs(4, 1, 7, 4, 1, 2);
  expect r == "YES", "impl test 3 failed";

  r := ElevatorOrStairs(749, 864, 931, 266, 94, 891);
  expect r == "NO", "impl test 4 failed";

  r := ElevatorOrStairs(719, 137, 307, 244, 724, 777);
  expect r == "NO", "impl test 5 failed";

  r := ElevatorOrStairs(608, 11, 980, 338, 208, 78);
  expect r == "YES", "impl test 6 failed";

  r := ElevatorOrStairs(571, 695, 153, 288, 64, 421);
  expect r == "NO", "impl test 7 failed";

  r := ElevatorOrStairs(837, 544, 703, 808, 549, 694);
  expect r == "YES", "impl test 8 failed";

  r := ElevatorOrStairs(271, 634, 606, 95, 39, 523);
  expect r == "YES", "impl test 9 failed";

  r := ElevatorOrStairs(1000, 999, 1000, 1000, 1000, 1000);
  expect r == "NO", "impl test 10 failed";

  print "All tests passed\n";
}
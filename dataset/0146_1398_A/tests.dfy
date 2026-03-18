predicate CanFormTriangle(x: int, y: int, z: int)
{
  x + y > z && x + z > y && y + z > x
}

predicate Sorted(a: seq<int>)
{
  forall i, j | 0 <= i && i <= j && j < |a| :: a[i] <= a[j]
}

// Top-level ensures predicate for found=true case
predicate EnsuresFound(a: seq<int>, result: (int, int, int))
{
  1 <= result.0 && result.0 < result.1 && result.1 < result.2 && result.2 <= |a| &&
  !CanFormTriangle(a[result.0 - 1], a[result.1 - 1], a[result.2 - 1])
}

// Top-level ensures predicate for found=false case
predicate EnsuresNotFound(a: seq<int>)
{
  forall i, j, k | 0 <= i && i < j && j < k && k < |a| ::
    CanFormTriangle(a[i], a[j], a[k])
}

method BadTriangle(a: seq<int>) returns (result: (int, int, int), found: bool)
  requires |a| >= 3
  requires Sorted(a)
  ensures found ==>
    1 <= result.0 && result.0 < result.1 && result.1 < result.2 && result.2 <= |a| &&
    !CanFormTriangle(a[result.0 - 1], a[result.1 - 1], a[result.2 - 1])
  ensures !found ==>
    forall i, j, k | 0 <= i && i < j && j < k && k < |a| ::
      CanFormTriangle(a[i], a[j], a[k])
{
  result := (0, 0, 0);
  found := false;
  var n := |a|;

  var x := a[0] + a[1] - a[n - 1];
  var y := a[0] - a[1] + a[n - 1];
  var z := -a[0] + a[1] + a[n - 1];
  if x <= 0 || y <= 0 || z <= 0 {
    result := (1, 2, n);
    found := true;
    return;
  }

  x := a[0] + a[n - 1] - a[n - 2];
  y := a[0] - a[n - 1] + a[n - 2];
  z := -a[0] + a[n - 1] + a[n - 2];
  if x <= 0 || y <= 0 || z <= 0 {
    result := (1, n - 1, n);
    found := true;
    return;
  }

  x := a[0] + a[1] - a[2];
  y := a[0] - a[1] + a[2];
  z := -a[0] + a[1] + a[2];
  if x <= 0 || y <= 0 || z <= 0 {
    result := (1, 2, 3);
    found := true;
    return;
  }

  x := a[n - 3] + a[n - 2] - a[n - 1];
  y := a[n - 3] - a[n - 2] + a[n - 1];
  z := -a[n - 3] + a[n - 2] + a[n - 1];
  if x <= 0 || y <= 0 || z <= 0 {
    result := (n - 2, n - 1, n);
    found := true;
    return;
  }
}

method Main()
{
  // ===== SPEC POSITIVE TESTS =====
  // Ensures predicates with correct outputs on small inputs

  // found=true: valid indices and triple cannot form a triangle
  expect EnsuresFound([1, 1, 3], (1, 2, 3)), "spec positive 1";   // 1+1=2 < 3
  expect EnsuresFound([1, 2, 5], (1, 2, 3)), "spec positive 2";   // 1+2=3 < 5
  expect EnsuresFound([1, 1, 4], (1, 2, 3)), "spec positive 3";   // 1+1=2 < 4
  expect EnsuresFound([1, 3, 5], (1, 2, 3)), "spec positive 4";   // 1+3=4 < 5
  expect EnsuresFound([2, 3, 5], (1, 2, 3)), "spec positive 5";   // 2+3=5, not > 5

  // found=false: all triples form valid triangles
  expect EnsuresNotFound([2, 2, 3]), "spec positive 6";            // 2+2=4 > 3
  expect EnsuresNotFound([3, 4, 5]), "spec positive 7";            // classic 3-4-5
  expect EnsuresNotFound([3, 3, 4]), "spec positive 8";            // 3+3=6 > 4

  // ===== SPEC NEGATIVE TESTS =====
  // Ensures predicates with WRONG outputs — spec must reject

  // Wrong results with i==j (indices not strictly increasing), mirrors Neg1-Neg10
  expect !EnsuresFound([1, 1, 3], (2, 2, 3)), "spec negative 1";  // Neg1: i==j
  expect !EnsuresFound([1, 2, 5], (2, 2, 3)), "spec negative 2";  // Neg6: i==j
  expect !EnsuresFound([1, 3, 5], (2, 2, 3)), "spec negative 3";  // Neg4: i==j
  expect !EnsuresFound([1, 1, 4], (2, 2, 3)), "spec negative 4";  // Neg5: i==j
  expect !EnsuresFound([2, 3, 5], (2, 2, 3)), "spec negative 5";  // Neg8: i==j

  // Wrong: claims "found" but the triple actually forms a valid triangle
  expect !EnsuresFound([2, 2, 3], (1, 2, 3)), "spec negative 6";  // 2+2>3, valid triangle

  // Wrong: claims "not found" but a bad triple exists
  expect !EnsuresNotFound([1, 1, 3]), "spec negative 7";           // 1+1<=3, bad triple exists

  // ===== IMPLEMENTATION TESTS =====

  var r1, f1 := BadTriangle([4, 6, 11, 11, 15, 18, 20]);
  expect f1 == true, "impl test 1a failed";
  expect r1 == (1, 2, 7), "impl test 1a result failed";

  var r2, f2 := BadTriangle([10, 10, 10, 11]);
  expect f2 == false, "impl test 1b failed";

  var r3, f3 := BadTriangle([1, 1, 1000000000]);
  expect f3 == true, "impl test 1c failed";
  expect r3 == (1, 2, 3), "impl test 1c result failed";

  var r4, f4 := BadTriangle([78788, 78788, 100000]);
  expect f4 == false, "impl test 2 failed";

  var r5, f5 := BadTriangle([78788, 78788, 157577]);
  expect f5 == true, "impl test 3 failed";
  expect r5 == (1, 2, 3), "impl test 3 result failed";

  var r6, f6 := BadTriangle([1, 7, 7, 7, 7, 9, 9, 9, 9, 9]);
  expect f6 == true, "impl test 4 failed";
  expect r6 == (1, 2, 10), "impl test 4 result failed";

  var r7, f7 := BadTriangle([1, 1, 1, 2, 2, 3]);
  expect f7 == true, "impl test 5 failed";
  expect r7 == (1, 2, 6), "impl test 5 result failed";

  var r8, f8 := BadTriangle([5623, 5624, 10000000]);
  expect f8 == true, "impl test 6 failed";
  expect r8 == (1, 2, 3), "impl test 6 result failed";

  var r9, f9 := BadTriangle([5739271, 5739272, 20000000]);
  expect f9 == true, "impl test 7 failed";
  expect r9 == (1, 2, 3), "impl test 7 result failed";

  var r10, f10 := BadTriangle([1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 4]);
  expect f10 == true, "impl test 8 failed";
  expect r10 == (1, 2, 14), "impl test 8 result failed";

  var r11, f11 := BadTriangle([1, 65535, 10000000]);
  expect f11 == true, "impl test 9 failed";
  expect r11 == (1, 2, 3), "impl test 9 result failed";

  var r12, f12 := BadTriangle([21, 78868, 80000]);
  expect f12 == true, "impl test 10 failed";
  expect r12 == (1, 2, 3), "impl test 10 result failed";

  var r13, f13 := BadTriangle([3, 4, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 32, 36, 39]);
  expect f13 == true, "impl test 11 failed";
  expect r13 == (1, 2, 15), "impl test 11 result failed";

  print "All tests passed\n";
}
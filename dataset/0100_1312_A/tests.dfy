predicate InscribedRegularPolygon(n: int, m: int, start: int, step: int)
  requires n > 0 && m > 0
{
  0 <= start < n && 1 <= step < n &&
  (forall j1, j2 | 0 <= j1 < m && 0 <= j2 < m && j1 != j2 ::
    (start + j1 * step) % n != (start + j2 * step) % n) &&
  (m * step) % n == 0
}

predicate CanInscribe(n: int, m: int)
  requires n > 0 && m > 0
{
  exists start, step | 0 <= start < n && 1 <= step < n ::
    InscribedRegularPolygon(n, m, start, step)
}

method TwoRegularPolygons(t: int, cases: seq<(int, int)>) returns (results: seq<bool>)
  requires |cases| == t
  requires forall i | 0 <= i < |cases| :: cases[i].0 > 0 && cases[i].1 > 0
  ensures |results| == |cases|
  ensures forall i | 0 <= i < |results| :: results[i] == CanInscribe(cases[i].0, cases[i].1)
{
  results := [];
  var i := 0;
  while i < |cases| {
    var (a, b) := cases[i];
    results := results + [a % b == 0];
    i := i + 1;
  }
}

method Main()
{
  // === SPEC POSITIVE TESTS ===
  // Testing: results[i] == CanInscribe(n, m) with correct outputs
  // Small inputs only to keep bounded quantifier enumeration fast.

  // From positive test 1: [(6,3)->true, (7,3)->false]
  expect CanInscribe(6, 3) == true, "spec positive 1a";
  expect CanInscribe(7, 3) == false, "spec positive 1b";

  // From positive test 4: [(6,3)->true]
  expect CanInscribe(6, 3) == true, "spec positive 4";

  // From positive test 5: [(7,3)->false]
  expect CanInscribe(7, 3) == false, "spec positive 5";

  // From positive test 6 (scaled, skipping (12,6) for size): [(12,4)->true, (12,3)->true]
  expect CanInscribe(12, 3) == true, "spec positive 6a";
  expect CanInscribe(12, 4) == true, "spec positive 6b";

  // From positive test 7 (scaled, keeping small cases): [(10,5)->true, (8,4)->true, (9,3)->true]
  expect CanInscribe(10, 5) == true, "spec positive 7a";
  expect CanInscribe(8, 4) == true, "spec positive 7b";
  expect CanInscribe(9, 3) == true, "spec positive 7c";

  // From positive test 8: [(4,3)->false]
  expect CanInscribe(4, 3) == false, "spec positive 8";

  // From positive test 10: [(6,4)->false, (6,5)->false, (8,3)->false, (9,6)->false]
  expect CanInscribe(6, 4) == false, "spec positive 10a";
  expect CanInscribe(6, 5) == false, "spec positive 10b";
  expect CanInscribe(8, 3) == false, "spec positive 10c";
  expect CanInscribe(9, 6) == false, "spec positive 10d";

  // Skipped: tests 2,3,9,11,13 (inputs too large for quantifier enumeration)

  // === SPEC NEGATIVE TESTS ===
  // Testing: wrong output does NOT satisfy results[i] == CanInscribe(n, m)
  // For each, the flipped element should mismatch CanInscribe.

  // From negative 1: (7,3) flipped from false to true
  expect CanInscribe(7, 3) != true, "spec negative 1";

  // From negative 4: (6,3) flipped from true to false
  expect CanInscribe(6, 3) != false, "spec negative 4";

  // From negative 5: (7,3) flipped from false to true
  expect CanInscribe(7, 3) != true, "spec negative 5";

  // From negative 6 (scaled from (12,6)->false to (6,3)->false): divisible case with wrong value false
  expect CanInscribe(6, 3) != false, "spec negative 6";

  // From negative 7 (scaled from (20,4)->false to (8,4)->false): divisible case with wrong value false
  expect CanInscribe(8, 4) != false, "spec negative 7";

  // From negative 8: (4,3) flipped from false to true
  expect CanInscribe(4, 3) != true, "spec negative 8";

  // From negative 10: (9,6) flipped from false to true
  expect CanInscribe(9, 6) != true, "spec negative 10";

  // Skipped: negatives 2,3,9 (inputs too large for quantifier enumeration)

  // === IMPLEMENTATION TESTS ===
  // Full-size inputs — method is fast (no quantifier enumeration).

  var r1 := TwoRegularPolygons(2, [(6, 3), (7, 3)]);
  expect r1 == [true, false], "impl test 1 failed";

  var r2 := TwoRegularPolygons(1, [(69, 68)]);
  expect r2 == [false], "impl test 2 failed";

  var r3 := TwoRegularPolygons(2, [(69, 68), (11, 9)]);
  expect r3 == [false, false], "impl test 3 failed";

  var r4 := TwoRegularPolygons(1, [(6, 3)]);
  expect r4 == [true], "impl test 4 failed";

  var r5 := TwoRegularPolygons(1, [(7, 3)]);
  expect r5 == [false], "impl test 5 failed";

  var r6 := TwoRegularPolygons(3, [(12, 4), (12, 3), (12, 6)]);
  expect r6 == [true, true, true], "impl test 6 failed";

  var r7 := TwoRegularPolygons(5, [(10, 5), (8, 4), (9, 3), (15, 5), (20, 4)]);
  expect r7 == [true, true, true, true, true], "impl test 7 failed";

  var r8 := TwoRegularPolygons(1, [(4, 3)]);
  expect r8 == [false], "impl test 8 failed";

  var r9 := TwoRegularPolygons(2, [(50, 25), (50, 10)]);
  expect r9 == [true, true], "impl test 9 failed";

  var r10 := TwoRegularPolygons(4, [(6, 4), (6, 5), (8, 3), (9, 6)]);
  expect r10 == [false, false, false, false], "impl test 10 failed";

  var r11 := TwoRegularPolygons(3, [(30, 5), (30, 6), (30, 10)]);
  expect r11 == [true, true, true], "impl test 11 failed";

  var r12 := TwoRegularPolygons(1, [(3, 3)]);
  expect r12 == [true], "impl test 12 failed";

  var r13 := TwoRegularPolygons(6, [(48, 3), (48, 4), (48, 6), (48, 8), (48, 12), (48, 16)]);
  expect r13 == [true, true, true, true, true, true], "impl test 13 failed";

  print "All tests passed\n";
}
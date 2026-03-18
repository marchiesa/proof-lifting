function FrogPosition(a: int, b: int, k: nat): real
  decreases k
{
  if k == 0 then 0.0
  else if (k - 1) % 2 == 0 then
    FrogPosition(a, b, k - 1) + a as real
  else
    FrogPosition(a, b, k - 1) - b as real
}

method FrogJumping(queries: seq<(int, int, int)>) returns (results: seq<real>)
  requires forall i | 0 <= i < |queries| :: queries[i].2 >= 0
  ensures |results| == |queries|
  ensures forall i | 0 <= i < |queries| ::
    results[i] == FrogPosition(queries[i].0, queries[i].1, queries[i].2)
{
  results := [];
  var i := 0;
  while i < |queries|
  {
    var (a, b, k) := queries[i];
    var f: real := k as real / 2.0;
    var ans: real := a as real * f - b as real * f;
    if k % 2 == 1 {
      ans := ans + a as real;
    }
    results := results + [ans];
    i := i + 1;
  }
}

method Main()
{
  // ============================================================
  // SPEC POSITIVE tests: FrogPosition(a, b, k) == expected
  // Small inputs to keep recursion tractable
  // ============================================================

  // From test pair 1, query (5,2,3) — same small values, k=3
  expect FrogPosition(5, 2, 3) == 8.0, "spec positive 1";

  // From test pair 1, query (100,1,4) — scaled to (3,1,4)
  expect FrogPosition(3, 1, 4) == 4.0, "spec positive 2";

  // From test pair 1, query (1,10,5) — scaled to (1,2,5)
  expect FrogPosition(1, 2, 5) == -1.0, "spec positive 3";

  // From test pair 1, query (1000000000,1,6) — scaled to (3,1,6)
  expect FrogPosition(3, 1, 6) == 6.0, "spec positive 4";

  // From test pair 1, query (1,1,1000000000) — scaled to (1,1,4)
  expect FrogPosition(1, 1, 4) == 0.0, "spec positive 5";

  // From test pair 1, query (1,1,999999999) — scaled to (1,1,3)
  expect FrogPosition(1, 1, 3) == 1.0, "spec positive 6";

  // From test pair 2, query (19280817,1,1) — scaled to (2,1,1)
  expect FrogPosition(2, 1, 1) == 2.0, "spec positive 7";

  // From test pair 3, query (598,56,799) — scaled to (3,2,3)
  expect FrogPosition(3, 2, 3) == 4.0, "spec positive 8";

  // From test pair 4, query (599,56,799) — scaled to (3,2,5)
  expect FrogPosition(3, 2, 5) == 5.0, "spec positive 9";

  // ============================================================
  // SPEC NEGATIVE tests: FrogPosition(a, b, k) != wrong_value
  // Each mirrors a negative test pair with a wrong output (off by 0.5 or other)
  // ============================================================

  // Analog of negative 1: (1,1,999999999) correct=1.0, wrong value=2.0
  expect FrogPosition(1, 1, 3) != 2.0, "spec negative 1";

  // Analog of negative 2: off by +0.5 (28921225.0 → 28921225.5)
  expect FrogPosition(2, 1, 1) != 2.5, "spec negative 2";

  // Analog of negative 3: off by +0.5 (217127.0 → 217127.5)
  expect FrogPosition(3, 2, 3) != 4.5, "spec negative 3";

  // Analog of negative 4: off by +0.5 (217527.5 → 217528.0)
  expect FrogPosition(3, 2, 5) != 5.5, "spec negative 4";

  // Additional: off by +0.5 from correct 8.0
  expect FrogPosition(5, 2, 3) != 8.5, "spec negative 5";

  // Additional: off by +0.5 from correct -1.0
  expect FrogPosition(1, 2, 5) != -0.5, "spec negative 6";

  // Additional: wrong value 1.0 for correct 0.0
  expect FrogPosition(1, 1, 4) != 1.0, "spec negative 7";

  // ============================================================
  // IMPLEMENTATION tests: call FrogJumping, check method output
  // Full-size inputs (the method runs in O(n), no recursion)
  // ============================================================

  // Test 1: 6 queries
  var results1 := FrogJumping([(5, 2, 3), (100, 1, 4), (1, 10, 5), (1000000000, 1, 6), (1, 1, 1000000000), (1, 1, 999999999)]);
  expect |results1| == 6, "impl test 1 length";
  expect results1[0] == 9.5, "impl test 1.0 failed";
  expect results1[1] == 198.0, "impl test 1.1 failed";
  expect results1[2] == -21.5, "impl test 1.2 failed";
  expect results1[3] == 2999999997.0, "impl test 1.3 failed";
  expect results1[4] == 0.0, "impl test 1.4 failed";
  expect results1[5] == 1.0, "impl test 1.5 failed";

  // Test 2
  var results2 := FrogJumping([(19280817, 1, 1)]);
  expect |results2| == 1, "impl test 2 length";
  expect results2[0] == 28921225.0, "impl test 2 failed";

  // Test 3
  var results3 := FrogJumping([(598, 56, 799)]);
  expect |results3| == 1, "impl test 3 length";
  expect results3[0] == 217127.0, "impl test 3 failed";

  // Test 4
  var results4 := FrogJumping([(599, 56, 799)]);
  expect |results4| == 1, "impl test 4 length";
  expect results4[0] == 217527.5, "impl test 4 failed";

  print "All tests passed\n";
}
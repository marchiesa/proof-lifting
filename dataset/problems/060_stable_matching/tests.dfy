// Stable Matching (Gale-Shapley) -- Runtime spec tests
// The spec guarantees: match_m.Length == n and forall i :: 0 <= i < n ==> 0 <= match_m[i] < n
// We test these postcondition properties on simulated results.

method Main() {
  // Postcondition: length == n and all entries in [0, n)

  // n=1: match_m = [0]
  var m1 := [0];
  expect |m1| == 1, "length == n for n=1";
  expect 0 <= m1[0] < 1, "match in valid range";

  // n=2: valid matching [0, 1]
  var m2a := [0, 1];
  expect |m2a| == 2, "length == n for n=2";
  expect 0 <= m2a[0] < 2, "man 0 matched to valid woman";
  expect 0 <= m2a[1] < 2, "man 1 matched to valid woman";

  // n=2: valid matching [1, 0]
  var m2b := [1, 0];
  expect |m2b| == 2, "length == n for n=2";
  expect 0 <= m2b[0] < 2, "man 0 matched to valid woman";
  expect 0 <= m2b[1] < 2, "man 1 matched to valid woman";

  // n=3: valid matching [2, 0, 1]
  var m3 := [2, 0, 1];
  expect |m3| == 3, "length == n for n=3";
  expect 0 <= m3[0] < 3 && 0 <= m3[1] < 3 && 0 <= m3[2] < 3, "all in valid range";

  // Invalid: out of range
  var bad1 := [0, 3];
  expect !(0 <= bad1[1] < 2), "3 not in [0,2)";

  // Invalid: negative
  var bad2 := [-1, 0];
  expect !(0 <= bad2[0] < 2), "-1 not in valid range";

  // In a correct stable matching, we expect it to be a permutation (each woman matched once)
  // This is implied by stability but not explicitly in the postcondition
  // Still, let's test permutation property for known good matchings
  var pm := [2, 0, 1];
  expect pm[0] != pm[1] && pm[1] != pm[2] && pm[0] != pm[2], "matching is injective";

  print "All spec tests passed\n";
}

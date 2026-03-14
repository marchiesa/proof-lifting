// Coin Change -- Runtime spec tests
// The spec only guarantees result >= -1 and result != -1 ==> result >= 0.
// There are no standalone spec predicates; we test the Inf() function and
// the postcondition properties.

function Inf(): int { 1000001 }

method Main() {
  // Inf function test
  expect Inf() == 1000001, "Inf sentinel value";
  expect Inf() > 0, "Inf is positive";

  // Postcondition shape testing:
  // For any valid result r, either r == -1 or r >= 0
  // We test this property on known values

  // result = -1 satisfies result >= -1
  var r1: int := -1;
  expect r1 >= -1, "-1 satisfies >= -1";

  // result = 0 satisfies both conditions
  var r2: int := 0;
  expect r2 >= -1, "0 satisfies >= -1";
  expect r2 != -1 ==> r2 >= 0, "0 satisfies conditional";

  // result = 3 (e.g., 3 coins) satisfies both conditions
  var r3: int := 3;
  expect r3 >= -1, "3 satisfies >= -1";
  expect r3 != -1 ==> r3 >= 0, "3 satisfies conditional";

  // result = -2 would NOT satisfy the postcondition
  var bad: int := -2;
  expect !(bad >= -1), "-2 violates >= -1 postcondition";

  print "All spec tests passed\n";
}

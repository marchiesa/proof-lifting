function Max0(x: int): int {
  if x < 0 then 0 else x
}

function WeightAfterHeight(weight: int, height: int,
                           u1: int, d1: int, u2: int, d2: int): int
{
  var afterGain  := weight + height;
  var afterStone1 := if height == d1 then Max0(afterGain - u1) else afterGain;
  var afterStone2 := if height == d2 then Max0(afterStone1 - u2) else afterStone1;
  afterStone2
}

function Heights(h: int): seq<int>
  decreases if h >= 0 then h + 1 else 0
{
  if h < 0 then []
  else [h] + Heights(h - 1)
}

function RollThrough(w: int, heights: seq<int>,
                     u1: int, d1: int, u2: int, d2: int): int
  decreases |heights|
{
  if |heights| == 0 then w
  else RollThrough(WeightAfterHeight(w, heights[0], u1, d1, u2, d2),
                   heights[1..], u1, d1, u2, d2)
}

method Snowball(w: int, h: int, u1: int, d1: int, u2: int, d2: int) returns (finalWeight: int)
  ensures finalWeight == RollThrough(w, Heights(h), u1, d1, u2, d2)
{
  finalWeight := w;
  var i := h;
  while i >= 0 {
    finalWeight := finalWeight + i;
    if i == d1 {
      finalWeight := finalWeight - u1;
      if finalWeight < 0 {
        finalWeight := 0;
      }
    }
    if i == d2 {
      finalWeight := finalWeight - u2;
      if finalWeight < 0 {
        finalWeight := 0;
      }
    }
    i := i - 1;
  }
}

method Main()
{
  // ===== SPEC POSITIVE TESTS =====
  // Test the top-level ensures predicate: RollThrough(w, Heights(h), u1, d1, u2, d2) == expected
  // Using tests with small h values (h <= 7)

  expect RollThrough(4, Heights(3), 1, 1, 1, 2) == 8, "spec positive 1";
  expect RollThrough(4, Heights(3), 9, 2, 0, 1) == 1, "spec positive 2";
  expect RollThrough(41, Heights(2), 1, 1, 67, 2) == 0, "spec positive 3";
  expect RollThrough(87, Heights(2), 10, 2, 76, 1) == 4, "spec positive 4";
  expect RollThrough(94, Heights(3), 71, 3, 12, 2) == 17, "spec positive 5";
  expect RollThrough(30, Heights(2), 88, 1, 2, 2) == 0, "spec positive 6";
  expect RollThrough(8, Heights(2), 29, 1, 23, 2) == 0, "spec positive 7";
  expect RollThrough(85, Heights(3), 47, 1, 92, 3) == 0, "spec positive 8";
  expect RollThrough(34, Heights(5), 82, 2, 52, 5) == 1, "spec positive 9";
  expect RollThrough(19, Heights(7), 14, 7, 28, 3) == 5, "spec positive 10";

  // ===== SPEC NEGATIVE TESTS =====
  // The spec should reject wrong outputs

  expect RollThrough(4, Heights(3), 1, 1, 1, 2) != 9, "spec negative 1";
  expect RollThrough(4, Heights(3), 9, 2, 0, 1) != 2, "spec negative 2";
  expect RollThrough(41, Heights(2), 1, 1, 67, 2) != 1, "spec negative 3";
  expect RollThrough(87, Heights(2), 10, 2, 76, 1) != 5, "spec negative 4";
  expect RollThrough(94, Heights(3), 71, 3, 12, 2) != 18, "spec negative 5";
  expect RollThrough(30, Heights(2), 88, 1, 2, 2) != 1, "spec negative 6";
  expect RollThrough(8, Heights(2), 29, 1, 23, 2) != 1, "spec negative 7";
  expect RollThrough(85, Heights(3), 47, 1, 92, 3) != 1, "spec negative 8";
  expect RollThrough(34, Heights(5), 82, 2, 52, 5) != 2, "spec negative 9";
  expect RollThrough(19, Heights(7), 14, 7, 28, 3) != 6, "spec negative 10";

  // ===== IMPLEMENTATION TESTS =====
  // Call the method and check results (full-size inputs are fine)

  var r: int;

  r := Snowball(4, 3, 1, 1, 1, 2);
  expect r == 8, "impl test 1 failed";

  r := Snowball(4, 3, 9, 2, 0, 1);
  expect r == 1, "impl test 2 failed";

  r := Snowball(41, 2, 1, 1, 67, 2);
  expect r == 0, "impl test 3 failed";

  r := Snowball(87, 2, 10, 2, 76, 1);
  expect r == 4, "impl test 4 failed";

  r := Snowball(94, 3, 71, 3, 12, 2);
  expect r == 17, "impl test 5 failed";

  r := Snowball(30, 2, 88, 1, 2, 2);
  expect r == 0, "impl test 6 failed";

  r := Snowball(8, 2, 29, 1, 23, 2);
  expect r == 0, "impl test 7 failed";

  r := Snowball(85, 3, 47, 1, 92, 3);
  expect r == 0, "impl test 8 failed";

  r := Snowball(34, 5, 82, 2, 52, 5);
  expect r == 1, "impl test 9 failed";

  r := Snowball(19, 7, 14, 7, 28, 3);
  expect r == 5, "impl test 10 failed";

  r := Snowball(43, 10, 72, 7, 49, 1);
  expect r == 0, "impl test 11 failed";

  r := Snowball(94, 30, 83, 11, 85, 27);
  expect r == 391, "impl test 12 failed";

  r := Snowball(19, 50, 36, 15, 90, 16);
  expect r == 1168, "impl test 13 failed";

  r := Snowball(29, 100, 30, 51, 28, 92);
  expect r == 5021, "impl test 14 failed";

  r := Snowball(71, 100, 56, 44, 12, 85);
  expect r == 5053, "impl test 15 failed";

  r := Snowball(80, 7, 17, 4, 96, 3);
  expect r == 3, "impl test 16 failed";

  r := Snowball(6, 10, 12, 5, 86, 4);
  expect r == 6, "impl test 17 failed";

  r := Snowball(94, 80, 44, 14, 26, 7);
  expect r == 3264, "impl test 18 failed";

  r := Snowball(24, 62, 24, 27, 48, 13);
  expect r == 1905, "impl test 19 failed";

  r := Snowball(98, 68, 94, 39, 69, 19);
  expect r == 2281, "impl test 20 failed";

  print "All tests passed\n";
}
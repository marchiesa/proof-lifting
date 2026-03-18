function AbsDiff(x: int, y: int): int
{
  if x >= y then x - y else y - x
}

function TwiceTriangleArea(x1: int, y1: int, x2: int, y2: int, x3: int, y3: int): int
{
  AbsDiff(x1 * (y2 - y3) + x2 * (y3 - y1) + x3 * (y1 - y2), 0)
}

function DistinctPastureAreas(a: seq<int>): set<int>
{
  set i: int, j: int
    | 0 <= i < |a| && 0 <= j < |a| && i != j
      && TwiceTriangleArea(a[i], 0, a[j], 0, 0, 1) > 0
    :: TwiceTriangleArea(a[i], 0, a[j], 0, 0, 1)
}

method BovineDilemma(a: seq<int>) returns (count: int)
  ensures count == |DistinctPastureAreas(a)|
{
  var s: set<int> := {};
  for i := 0 to |a| {
    for j := 0 to |a| {
      if a[i] > a[j] {
        s := s + {a[i] - a[j]};
      }
    }
  }
  count := |s|;
}

method Main()
{
  // === SPEC POSITIVE TESTS ===
  // Test ensures: count == |DistinctPastureAreas(a)| with small inputs

  // From Test 1.4: [1, 2] → 1
  expect |DistinctPastureAreas([1, 2])| == 1, "spec positive 1";

  // From Test 1.5/3.1: single element → 0
  expect |DistinctPastureAreas([3])| == 0, "spec positive 2";

  // From Test 5: [1, 2, 3] → 2
  expect |DistinctPastureAreas([1, 2, 3])| == 2, "spec positive 3";

  // From Test 1.2: [1, 3, 5] → 2
  expect |DistinctPastureAreas([1, 3, 5])| == 2, "spec positive 4";

  // From Test 3.3: [3, 5] → 1
  expect |DistinctPastureAreas([3, 5])| == 1, "spec positive 5";

  // From Test 7: single element → 0
  expect |DistinctPastureAreas([5])| == 0, "spec positive 6";

  // Empty sequence → 0
  expect |DistinctPastureAreas([])| == 0, "spec positive 7";

  // === SPEC NEGATIVE TESTS ===
  // Test that wrong outputs are rejected by the spec

  // Neg 2 scaled: [1, 2] correct=1, wrong=2
  expect !(|DistinctPastureAreas([1, 2])| == 2), "spec negative 1";

  // Neg 3 scaled: [3] correct=0, wrong=1
  expect !(|DistinctPastureAreas([3])| == 1), "spec negative 2";

  // Neg 5: [1, 2, 3] correct=2, wrong=3
  expect !(|DistinctPastureAreas([1, 2, 3])| == 3), "spec negative 3";

  // Neg 7 scaled: [5] correct=0, wrong=1
  expect !(|DistinctPastureAreas([5])| == 1), "spec negative 4";

  // Neg 6 scaled: [1, 3, 5] correct=2, wrong=3
  expect !(|DistinctPastureAreas([1, 3, 5])| == 3), "spec negative 5";

  // Neg 4 scaled: [3, 5] correct=1, wrong=2
  expect !(|DistinctPastureAreas([3, 5])| == 2), "spec negative 6";

  // Neg 8 scaled: [1, 2, 3] correct=2, wrong=1
  expect !(|DistinctPastureAreas([1, 2, 3])| == 1), "spec negative 7";

  // === IMPLEMENTATION TESTS ===
  var r: int;

  // Test 1.1
  r := BovineDilemma([1, 2, 4, 5]);
  expect r == 4, "impl test 1.1 failed";

  // Test 1.2
  r := BovineDilemma([1, 3, 5]);
  expect r == 2, "impl test 1.2 failed";

  // Test 1.3
  r := BovineDilemma([2, 6, 8]);
  expect r == 3, "impl test 1.3 failed";

  // Test 1.4
  r := BovineDilemma([1, 2]);
  expect r == 1, "impl test 1.4 failed";

  // Test 1.5
  r := BovineDilemma([50]);
  expect r == 0, "impl test 1.5 failed";

  // Test 1.6
  r := BovineDilemma([3, 4, 5, 6, 8]);
  expect r == 5, "impl test 1.6 failed";

  // Test 1.7
  r := BovineDilemma([1, 25, 26]);
  expect r == 3, "impl test 1.7 failed";

  // Test 1.8
  r := BovineDilemma([1, 2, 4, 8, 16, 32]);
  expect r == 15, "impl test 1.8 failed";

  // Test 2
  r := BovineDilemma([1, 50]);
  expect r == 1, "impl test 2 failed";

  // Test 3.1
  r := BovineDilemma([7]);
  expect r == 0, "impl test 3.1 failed";

  // Test 3.2
  r := BovineDilemma([50]);
  expect r == 0, "impl test 3.2 failed";

  // Test 3.3
  r := BovineDilemma([3, 5]);
  expect r == 1, "impl test 3.3 failed";

  // Test 4
  r := BovineDilemma([2, 5, 7, 10]);
  expect r == 4, "impl test 4 failed";

  // Test 5
  r := BovineDilemma([1, 2, 3]);
  expect r == 2, "impl test 5 failed";

  // Test 6
  r := BovineDilemma([1, 3, 6, 10, 15]);
  expect r == 8, "impl test 6 failed";

  // Test 7
  r := BovineDilemma([25]);
  expect r == 0, "impl test 7 failed";

  // Test 8
  r := BovineDilemma([1, 2, 3, 4, 5, 6]);
  expect r == 5, "impl test 8 failed";

  // Test 9
  r := BovineDilemma([2, 4, 8, 16, 32, 48, 50]);
  expect r == 18, "impl test 9 failed";

  // Test 10
  r := BovineDilemma([1, 5, 10, 15, 20, 25, 30, 35, 40, 50]);
  expect r == 18, "impl test 10 failed";

  // Test 11
  r := BovineDilemma([3, 7, 11, 13, 19, 23, 29, 31]);
  expect r == 13, "impl test 11 failed";

  print "All tests passed\n";
}
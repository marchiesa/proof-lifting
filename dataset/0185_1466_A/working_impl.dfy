method BovineDilemma(a: seq<int>) returns (count: int)
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
  // Test 1 cases
  var r := BovineDilemma([1, 2, 4, 5]);
  expect r == 4, "Test 1.1 failed";

  r := BovineDilemma([1, 3, 5]);
  expect r == 2, "Test 1.2 failed";

  r := BovineDilemma([2, 6, 8]);
  expect r == 3, "Test 1.3 failed";

  r := BovineDilemma([1, 2]);
  expect r == 1, "Test 1.4 failed";

  r := BovineDilemma([50]);
  expect r == 0, "Test 1.5 failed";

  r := BovineDilemma([3, 4, 5, 6, 8]);
  expect r == 5, "Test 1.6 failed";

  r := BovineDilemma([1, 25, 26]);
  expect r == 3, "Test 1.7 failed";

  r := BovineDilemma([1, 2, 4, 8, 16, 32]);
  expect r == 15, "Test 1.8 failed";

  // Test 2
  r := BovineDilemma([1, 50]);
  expect r == 1, "Test 2 failed";

  // Test 3 cases
  r := BovineDilemma([7]);
  expect r == 0, "Test 3.1 failed";

  r := BovineDilemma([50]);
  expect r == 0, "Test 3.2 failed";

  r := BovineDilemma([3, 5]);
  expect r == 1, "Test 3.3 failed";

  // Test 4
  r := BovineDilemma([2, 5, 7, 10]);
  expect r == 4, "Test 4 failed";

  // Test 5
  r := BovineDilemma([1, 2, 3]);
  expect r == 2, "Test 5 failed";

  // Test 6
  r := BovineDilemma([1, 3, 6, 10, 15]);
  expect r == 8, "Test 6 failed";

  // Test 7
  r := BovineDilemma([25]);
  expect r == 0, "Test 7 failed";

  // Test 8
  r := BovineDilemma([1, 2, 3, 4, 5, 6]);
  expect r == 5, "Test 8 failed";

  // Test 9
  r := BovineDilemma([2, 4, 8, 16, 32, 48, 50]);
  expect r == 18, "Test 9 failed";

  // Test 10
  r := BovineDilemma([1, 5, 10, 15, 20, 25, 30, 35, 40, 50]);
  expect r == 18, "Test 10 failed";

  // Test 11
  r := BovineDilemma([3, 7, 11, 13, 19, 23, 29, 31]);
  expect r == 13, "Test 11 failed";

  print "All tests passed\n";
}
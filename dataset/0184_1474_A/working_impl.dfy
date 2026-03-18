method PuzzleFromTheFuture(n: int, b: seq<int>) returns (a: seq<int>)
{
  a := [1];
  var i := 1;
  while i < n
  {
    if a[i - 1] + b[i - 1] == 1 + b[i] {
      a := a + [0];
    } else {
      a := a + [1];
    }
    i := i + 1;
  }
}

method Main()
{
  // Test 1.1: n=1, b="0"
  var r := PuzzleFromTheFuture(1, [0]);
  expect r == [1], "Test 1.1 failed";

  // Test 1.2: n=3, b="011"
  r := PuzzleFromTheFuture(3, [0, 1, 1]);
  expect r == [1, 1, 0], "Test 1.2 failed";

  // Test 1.3: n=3, b="110"
  r := PuzzleFromTheFuture(3, [1, 1, 0]);
  expect r == [1, 0, 0], "Test 1.3 failed";

  // Test 1.4: n=6, b="111000"
  r := PuzzleFromTheFuture(6, [1, 1, 1, 0, 0, 0]);
  expect r == [1, 0, 1, 1, 0, 1], "Test 1.4 failed";

  // Test 1.5: n=6, b="001011"
  r := PuzzleFromTheFuture(6, [0, 0, 1, 0, 1, 1]);
  expect r == [1, 0, 1, 1, 1, 0], "Test 1.5 failed";

  // Test 2.1: n=1, b="0"
  r := PuzzleFromTheFuture(1, [0]);
  expect r == [1], "Test 2.1 failed";

  // Test 2.2: n=1, b="1"
  r := PuzzleFromTheFuture(1, [1]);
  expect r == [1], "Test 2.2 failed";

  // Test 2.3: n=2, b="01"
  r := PuzzleFromTheFuture(2, [0, 1]);
  expect r == [1, 1], "Test 2.3 failed";

  // Test 3.1: n=5, b="10101"
  r := PuzzleFromTheFuture(5, [1, 0, 1, 0, 1]);
  expect r == [1, 1, 1, 1, 1], "Test 3.1 failed";

  // Test 4.1: n=3, b="010"
  r := PuzzleFromTheFuture(3, [0, 1, 0]);
  expect r == [1, 1, 1], "Test 4.1 failed";

  // Test 4.2: n=4, b="1100"
  r := PuzzleFromTheFuture(4, [1, 1, 0, 0]);
  expect r == [1, 0, 0, 1], "Test 4.2 failed";

  // Test 5.1: n=1, b="1"
  r := PuzzleFromTheFuture(1, [1]);
  expect r == [1], "Test 5.1 failed";

  // Test 6.1: n=2, b="00"
  r := PuzzleFromTheFuture(2, [0, 0]);
  expect r == [1, 0], "Test 6.1 failed";

  // Test 6.2: n=2, b="11"
  r := PuzzleFromTheFuture(2, [1, 1]);
  expect r == [1, 0], "Test 6.2 failed";

  // Test 7.1: n=4, b="0110"
  r := PuzzleFromTheFuture(4, [0, 1, 1, 0]);
  expect r == [1, 1, 0, 0], "Test 7.1 failed";

  // Test 8.1: n=1, b="0"
  r := PuzzleFromTheFuture(1, [0]);
  expect r == [1], "Test 8.1 failed";

  // Test 8.2: n=2, b="10"
  r := PuzzleFromTheFuture(2, [1, 0]);
  expect r == [1, 1], "Test 8.2 failed";

  // Test 8.3: n=3, b="101"
  r := PuzzleFromTheFuture(3, [1, 0, 1]);
  expect r == [1, 1, 1], "Test 8.3 failed";

  // Test 9.1: n=5, b="00000"
  r := PuzzleFromTheFuture(5, [0, 0, 0, 0, 0]);
  expect r == [1, 0, 1, 0, 1], "Test 9.1 failed";

  // Test 9.2: n=5, b="11111"
  r := PuzzleFromTheFuture(5, [1, 1, 1, 1, 1]);
  expect r == [1, 0, 1, 0, 1], "Test 9.2 failed";

  // Test 10.1: n=6, b="101010"
  r := PuzzleFromTheFuture(6, [1, 0, 1, 0, 1, 0]);
  expect r == [1, 1, 1, 1, 1, 1], "Test 10.1 failed";

  // Test 11.1: n=1, b="0"
  r := PuzzleFromTheFuture(1, [0]);
  expect r == [1], "Test 11.1 failed";

  // Test 11.2: n=1, b="1"
  r := PuzzleFromTheFuture(1, [1]);
  expect r == [1], "Test 11.2 failed";

  // Test 11.3: n=2, b="01"
  r := PuzzleFromTheFuture(2, [0, 1]);
  expect r == [1, 1], "Test 11.3 failed";

  // Test 11.4: n=3, b="110"
  r := PuzzleFromTheFuture(3, [1, 1, 0]);
  expect r == [1, 0, 0], "Test 11.4 failed";

  print "All tests passed\n";
}
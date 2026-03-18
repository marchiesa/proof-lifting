method EvenArray(a: seq<int>) returns (result: int)
{
  var badEven := 0;
  var badOdd := 0;
  var i := 0;
  while i < |a|
  {
    if i % 2 != a[i] % 2 && i % 2 == 0 {
      badEven := badEven + 1;
    } else if i % 2 != a[i] % 2 && i % 2 == 1 {
      badOdd := badOdd + 1;
    }
    i := i + 1;
  }
  if badEven == badOdd {
    result := badEven;
  } else {
    result := -1;
  }
}

method Main()
{
  var r: int;

  // Test 1
  r := EvenArray([3, 2, 7, 6]);
  expect r == 2, "Test 1a failed";
  r := EvenArray([3, 2, 6]);
  expect r == 1, "Test 1b failed";
  r := EvenArray([7]);
  expect r == -1, "Test 1c failed";
  r := EvenArray([4, 9, 2, 1, 18, 3, 0]);
  expect r == 0, "Test 1d failed";

  // Test 2 (seven single-element [0] cases)
  r := EvenArray([0]);
  expect r == 0, "Test 2a failed";
  r := EvenArray([0]);
  expect r == 0, "Test 2b failed";
  r := EvenArray([0]);
  expect r == 0, "Test 2c failed";
  r := EvenArray([0]);
  expect r == 0, "Test 2d failed";
  r := EvenArray([0]);
  expect r == 0, "Test 2e failed";
  r := EvenArray([0]);
  expect r == 0, "Test 2f failed";
  r := EvenArray([0]);
  expect r == 0, "Test 2g failed";

  // Test 3
  r := EvenArray([0, 5, 2, 1]);
  expect r == 0, "Test 3 failed";

  // Test 4
  r := EvenArray([3, 2, 7, 6]);
  expect r == 2, "Test 4 failed";

  // Test 5
  r := EvenArray([7]);
  expect r == -1, "Test 5a failed";
  r := EvenArray([4, 3]);
  expect r == 0, "Test 5b failed";
  r := EvenArray([1, 2, 3]);
  expect r == -1, "Test 5c failed";

  // Test 6
  r := EvenArray([0]);
  expect r == 0, "Test 6 failed";

  // Test 7
  r := EvenArray([1, 3, 5, 7, 9]);
  expect r == -1, "Test 7 failed";

  // Test 8
  r := EvenArray([2, 4, 6, 8, 10, 12]);
  expect r == -1, "Test 8a failed";
  r := EvenArray([1, 3, 5, 7, 9, 11]);
  expect r == -1, "Test 8b failed";

  // Test 9
  r := EvenArray([0, 1, 2, 3, 4, 5, 6, 7]);
  expect r == 0, "Test 9 failed";

  // Test 10
  r := EvenArray([2, 1, 0]);
  expect r == 0, "Test 10 failed";

  // Test 11
  r := EvenArray([1, 2]);
  expect r == 1, "Test 11a failed";
  r := EvenArray([2, 1]);
  expect r == 0, "Test 11b failed";
  r := EvenArray([0, 0]);
  expect r == -1, "Test 11c failed";
  r := EvenArray([1, 1]);
  expect r == -1, "Test 11d failed";
  r := EvenArray([0, 1]);
  expect r == 0, "Test 11e failed";

  // Test 12
  r := EvenArray([50, 49, 48, 47, 46, 45, 44, 43, 42, 41]);
  expect r == 0, "Test 12 failed";

  print "All tests passed\n";
}
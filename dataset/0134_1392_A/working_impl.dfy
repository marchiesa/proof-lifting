method OmkarAndPassword(a: seq<int>) returns (result: int)
{
  var lo := a[0];
  var hi := a[0];
  var i := 1;
  while i < |a|
  {
    if a[i] < lo { lo := a[i]; }
    if a[i] > hi { hi := a[i]; }
    i := i + 1;
  }
  if lo == hi {
    return |a|;
  } else {
    return 1;
  }
}

method Main()
{
  var r: int;

  // Test 1
  r := OmkarAndPassword([2, 1, 3, 1]);
  expect r == 1, "Test 1a failed";
  r := OmkarAndPassword([420, 420]);
  expect r == 2, "Test 1b failed";

  // Test 2
  r := OmkarAndPassword([1, 7, 7, 1, 7, 1]);
  expect r == 1, "Test 2a failed";
  r := OmkarAndPassword([3, 3]);
  expect r == 2, "Test 2b failed";
  r := OmkarAndPassword([1, 1000000000, 1000000000, 2, 2, 1, 2, 2]);
  expect r == 1, "Test 2c failed";
  r := OmkarAndPassword([420, 69]);
  expect r == 1, "Test 2d failed";
  r := OmkarAndPassword([1, 3, 5, 7, 9, 2, 4, 6, 8, 10]);
  expect r == 1, "Test 2e failed";
  r := OmkarAndPassword([6, 16, 7, 6, 1]);
  expect r == 1, "Test 2f failed";
  r := OmkarAndPassword([16, 16, 16]);
  expect r == 3, "Test 2g failed";
  r := OmkarAndPassword([1, 2, 9, 8, 4]);
  expect r == 1, "Test 2h failed";

  // Test 3
  r := OmkarAndPassword([529035968, 529035968, 529035968, 529035968, 529035968, 529035968, 529035968]);
  expect r == 7, "Test 3 failed";

  // Test 4
  r := OmkarAndPassword([3, 4, 7]);
  expect r == 1, "Test 4 failed";

  // Test 5
  r := OmkarAndPassword([1, 2, 1, 2]);
  expect r == 1, "Test 5 failed";

  // Test 6
  r := OmkarAndPassword([3, 1, 2]);
  expect r == 1, "Test 6 failed";

  // Test 7
  r := OmkarAndPassword([4, 4, 2, 2]);
  expect r == 1, "Test 7 failed";

  // Test 8
  r := OmkarAndPassword([1, 2, 3]);
  expect r == 1, "Test 8 failed";

  // Test 9
  r := OmkarAndPassword([2, 4, 6, 10]);
  expect r == 1, "Test 9 failed";

  // Test 10
  r := OmkarAndPassword([5, 4, 9, 9, 9]);
  expect r == 1, "Test 10 failed";

  // Test 11
  r := OmkarAndPassword([2, 2, 3, 3, 3]);
  expect r == 1, "Test 11 failed";

  // Test 12
  r := OmkarAndPassword([3, 4, 4, 4]);
  expect r == 1, "Test 12 failed";

  // Test 13
  r := OmkarAndPassword([4, 1, 5, 5, 5, 5]);
  expect r == 1, "Test 13 failed";

  // Test 14
  r := OmkarAndPassword([1, 1, 2, 4]);
  expect r == 1, "Test 14 failed";

  // Test 15
  r := OmkarAndPassword([1, 1, 1, 1, 1, 1, 1, 1, 1, 2]);
  expect r == 1, "Test 15 failed";

  // Test 16
  r := OmkarAndPassword([5, 5, 5, 3, 2]);
  expect r == 1, "Test 16 failed";

  // Test 17
  r := OmkarAndPassword([1, 2, 3, 4, 11]);
  expect r == 1, "Test 17 failed";

  // Test 18
  r := OmkarAndPassword([1, 3, 4]);
  expect r == 1, "Test 18 failed";

  // Test 19
  r := OmkarAndPassword([2, 2, 1, 2, 2]);
  expect r == 1, "Test 19 failed";

  // Test 20
  r := OmkarAndPassword([5, 6, 11, 11, 11]);
  expect r == 1, "Test 20 failed";

  print "All tests passed\n";
}
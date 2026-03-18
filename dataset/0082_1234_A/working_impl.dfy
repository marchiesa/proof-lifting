method EqualizePrice(a: seq<int>) returns (price: int)
{
  var s := 0;
  var n := |a|;
  var i := 0;
  while i < n
  {
    s := s + a[i];
    i := i + 1;
  }
  price := (s + n - 1) / n;
}

method Main()
{
  // Test 1, case 1: [1,2,3,4,5] -> 3
  var r1 := EqualizePrice([1, 2, 3, 4, 5]);
  expect r1 == 3, "Test 1.1 failed";

  // Test 1, case 2: [1,2,2] -> 2
  var r2 := EqualizePrice([1, 2, 2]);
  expect r2 == 2, "Test 1.2 failed";

  // Test 1, case 3: [1,1,1,1] -> 1
  var r3 := EqualizePrice([1, 1, 1, 1]);
  expect r3 == 1, "Test 1.3 failed";

  // Test 2: [777,1] -> 389
  var r4 := EqualizePrice([777, 1]);
  expect r4 == 389, "Test 2 failed";

  // Test 3: [2441139] -> 2441139
  var r5 := EqualizePrice([2441139]);
  expect r5 == 2441139, "Test 3 failed";

  // Test 4, case 1: [1,2,3,4,5] -> 3
  var r6 := EqualizePrice([1, 2, 3, 4, 5]);
  expect r6 == 3, "Test 4.1 failed";

  // Test 4, case 2: [1,2,3] -> 2
  var r7 := EqualizePrice([1, 2, 3]);
  expect r7 == 2, "Test 4.2 failed";

  // Test 4, case 3: [777,778] -> 778
  var r8 := EqualizePrice([777, 778]);
  expect r8 == 778, "Test 4.3 failed";

  // Test 5: [777,778] -> 778
  var r9 := EqualizePrice([777, 778]);
  expect r9 == 778, "Test 5 failed";

  print "All tests passed\n";
}
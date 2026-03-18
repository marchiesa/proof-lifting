method YetAnotherBookshelf(a: seq<int>) returns (moves: int)
{
  var n := |a|;
  var one := 0;
  var i := 0;
  while i < n {
    one := one + a[i];
    i := i + 1;
  }

  if one == 0 {
    return 0;
  }

  var first := 0;
  i := 0;
  while i < n {
    if a[i] == 1 {
      first := i;
      break;
    }
    i := i + 1;
  }

  var last := n;
  i := n - 1;
  while i >= 0 {
    if a[i] == 1 {
      last := i;
      break;
    }
    i := i - 1;
  }

  moves := last - first - one + 1;
}

method Main()
{
  // Test 1, case 1
  var r1 := YetAnotherBookshelf([0, 0, 1, 0, 1, 0, 1]);
  expect r1 == 2, "Test 1.1 failed";

  // Test 1, case 2
  var r2 := YetAnotherBookshelf([1, 0, 0]);
  expect r2 == 0, "Test 1.2 failed";

  // Test 1, case 3
  var r3 := YetAnotherBookshelf([1, 1, 0, 0, 1]);
  expect r3 == 2, "Test 1.3 failed";

  // Test 1, case 4
  var r4 := YetAnotherBookshelf([1, 0, 0, 0, 0, 1]);
  expect r4 == 4, "Test 1.4 failed";

  // Test 1, case 5
  var r5 := YetAnotherBookshelf([1, 1, 0, 1, 1]);
  expect r5 == 1, "Test 1.5 failed";

  // Test 2
  var r6 := YetAnotherBookshelf([0, 0, 0, 1, 1, 1, 1, 1]);
  expect r6 == 0, "Test 2 failed";

  // Test 3
  var r7 := YetAnotherBookshelf([1]);
  expect r7 == 0, "Test 3 failed";

  // Test 4
  var r8 := YetAnotherBookshelf([0, 0, 1, 0, 1]);
  expect r8 == 1, "Test 4 failed";

  // Test 5
  var r9 := YetAnotherBookshelf([1, 1, 1]);
  expect r9 == 0, "Test 5 failed";

  // Test 6
  var r10 := YetAnotherBookshelf([1, 0, 0, 1, 0, 1, 0, 0, 1, 1]);
  expect r10 == 5, "Test 6 failed";

  // Test 7
  var r11 := YetAnotherBookshelf([0, 1, 0, 0, 0, 1]);
  expect r11 == 3, "Test 7 failed";

  // Test 8, case 1
  var r12 := YetAnotherBookshelf([1, 0, 0, 1]);
  expect r12 == 2, "Test 8.1 failed";

  // Test 8, case 2
  var r13 := YetAnotherBookshelf([0, 1, 0]);
  expect r13 == 0, "Test 8.2 failed";

  // Test 9
  var r14 := YetAnotherBookshelf([0, 0, 0, 1, 0, 0, 0, 0]);
  expect r14 == 0, "Test 9 failed";

  // Test 10, case 1
  var r15 := YetAnotherBookshelf([1, 0, 1, 0, 1]);
  expect r15 == 2, "Test 10.1 failed";

  // Test 10, case 2
  var r16 := YetAnotherBookshelf([1, 1]);
  expect r16 == 0, "Test 10.2 failed";

  // Test 10, case 3
  var r17 := YetAnotherBookshelf([0, 1, 1, 0]);
  expect r17 == 0, "Test 10.3 failed";

  // Test 11
  var r18 := YetAnotherBookshelf([1, 0, 1, 0, 1, 0, 1, 0, 1, 0]);
  expect r18 == 4, "Test 11 failed";

  // Test 12, case 1
  var r19 := YetAnotherBookshelf([0, 1, 0, 0, 1, 0, 1]);
  expect r19 == 3, "Test 12.1 failed";

  // Test 12, case 2
  var r20 := YetAnotherBookshelf([1, 1, 0, 0, 1, 1]);
  expect r20 == 2, "Test 12.2 failed";

  print "All tests passed\n";
}
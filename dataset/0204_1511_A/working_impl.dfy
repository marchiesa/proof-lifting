method ReviewSite(n: int, r: seq<int>) returns (maxUpvotes: int)
{
  var count := 0;
  var i := 0;
  while i < |r|
  {
    if r[i] == 1 || r[i] == 3 {
      count := count + 1;
    }
    i := i + 1;
  }
  return count;
}

method Main()
{
  // Test 1, case 1: n=1, r=[2] -> 0
  var r1 := ReviewSite(1, [2]);
  expect r1 == 0, "Test 1.1 failed";

  // Test 1, case 2: n=3, r=[1,2,3] -> 2
  var r2 := ReviewSite(3, [1, 2, 3]);
  expect r2 == 2, "Test 1.2 failed";

  // Test 1, case 3: n=5, r=[1,1,1,1,1] -> 5
  var r3 := ReviewSite(5, [1, 1, 1, 1, 1]);
  expect r3 == 5, "Test 1.3 failed";

  // Test 1, case 4: n=3, r=[3,3,2] -> 2
  var r4 := ReviewSite(3, [3, 3, 2]);
  expect r4 == 2, "Test 1.4 failed";

  // Test 2: n=1, r=[1] -> 1 (repeated 9 times, all identical)
  var r5 := ReviewSite(1, [1]);
  expect r5 == 1, "Test 2 failed";

  // Test 3: n=1, r=[2] -> 0
  var r6 := ReviewSite(1, [2]);
  expect r6 == 0, "Test 3 failed";

  // Test 4: n=1, r=[1] -> 1
  var r7 := ReviewSite(1, [1]);
  expect r7 == 1, "Test 4 failed";

  // Test 5: n=1, r=[3] -> 1
  var r8 := ReviewSite(1, [3]);
  expect r8 == 1, "Test 5 failed";

  // Test 6: n=3, r=[3,3,3] -> 3
  var r9 := ReviewSite(3, [3, 3, 3]);
  expect r9 == 3, "Test 6 failed";

  // Test 7: n=5, r=[1,2,3,1,2] -> 3
  var r10 := ReviewSite(5, [1, 2, 3, 1, 2]);
  expect r10 == 3, "Test 7 failed";

  // Test 8: n=7, r=[3,3,3,3,3,3,3] -> 7
  var r11 := ReviewSite(7, [3, 3, 3, 3, 3, 3, 3]);
  expect r11 == 7, "Test 8 failed";

  // Test 9: n=10, r=[1,1,1,2,2,2,3,3,3,3] -> 7
  var r12 := ReviewSite(10, [1, 1, 1, 2, 2, 2, 3, 3, 3, 3]);
  expect r12 == 7, "Test 9 failed";

  // Test 10: n=6, r=[2,2,2,3,3,3] -> 3
  var r13 := ReviewSite(6, [2, 2, 2, 3, 3, 3]);
  expect r13 == 3, "Test 10 failed";

  // Test 11: n=8, r=[3,1,3,2,3,1,3,2] -> 6
  var r14 := ReviewSite(8, [3, 1, 3, 2, 3, 1, 3, 2]);
  expect r14 == 6, "Test 11 failed";

  // Test 12: n=4, r=[2,3,1,3] -> 3
  var r15 := ReviewSite(4, [2, 3, 1, 3]);
  expect r15 == 3, "Test 12 failed";

  print "All tests passed\n";
}
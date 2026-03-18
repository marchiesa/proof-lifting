method Tram(n: int, a: seq<int>, b: seq<int>) returns (capacity: int)
{
  var current := 0;
  capacity := 0;
  var i := 0;
  while i < n
  {
    current := current - a[i] + b[i];
    if current > capacity {
      capacity := current;
    }
    i := i + 1;
  }
}

method Main()
{
  // Test 1
  var r1 := Tram(4, [0,2,4,4], [3,5,2,0]);
  expect r1 == 6, "Test 1 failed";

  // Test 2
  var r2 := Tram(5, [0,4,6,5,4], [4,6,5,4,0]);
  expect r2 == 6, "Test 2 failed";

  // Test 3
  var r3 := Tram(10, [0,1,10,5,0,3,8,0,10,9], [5,7,8,3,5,3,8,6,1,0]);
  expect r3 == 18, "Test 3 failed";

  // Test 4
  var r4 := Tram(3, [0,1,1], [1,1,0]);
  expect r4 == 1, "Test 4 failed";

  // Test 5
  var r5 := Tram(4, [0,0,1,1], [1,1,0,0]);
  expect r5 == 2, "Test 5 failed";

  // Test 6
  var r6 := Tram(3, [0,0,0], [0,0,0]);
  expect r6 == 0, "Test 6 failed";

  // Test 7
  var r7 := Tram(3, [0,1000,1000], [1000,1000,0]);
  expect r7 == 1000, "Test 7 failed";

  // Test 8
  var r8 := Tram(5, [0,73,189,766,0], [73,189,766,0,0]);
  expect r8 == 766, "Test 8 failed";

  // Test 9
  var r9 := Tram(5, [0,0,0,0,1], [0,0,0,1,0]);
  expect r9 == 1, "Test 9 failed";

  // Test 10
  var r10 := Tram(5, [0,917,904,1000,11], [917,923,992,0,0]);
  expect r10 == 1011, "Test 10 failed";

  // Test 11
  var r11 := Tram(5, [0,1,2,1,2], [1,2,1,2,0]);
  expect r11 == 2, "Test 11 failed";

  // Test 12
  var r12 := Tram(5, [0,0,0,0,0], [0,0,0,0,0]);
  expect r12 == 0, "Test 12 failed";

  // Test 13
  var r13 := Tram(20, [0,2,2,5,2,6,2,0,7,8,10,2,6,1,0,8,6,6,1,3], [7,1,2,7,6,10,4,4,4,0,6,1,1,7,3,7,3,3,1,0]);
  expect r13 == 22, "Test 13 failed";

  // Test 14
  var r14 := Tram(5, [0,1000,1000,1000,1000], [1000,1000,1000,1000,0]);
  expect r14 == 1000, "Test 14 failed";

  // Test 15
  var r15 := Tram(10, [0,258,389,249,196,478,994,1000,769,0], [592,598,203,836,635,482,987,0,0,0]);
  expect r15 == 1776, "Test 15 failed";

  // Test 16
  var r16 := Tram(10, [0,1,0,0,0,0,1,0,1,1], [1,0,0,0,0,1,1,1,0,0]);
  expect r16 == 2, "Test 16 failed";

  // Test 17
  var r17 := Tram(10, [0,926,938,931,937,983,908,997,945,988], [926,938,931,964,989,936,949,932,988,0]);
  expect r17 == 1016, "Test 17 failed";

  // Test 18
  var r18 := Tram(10, [0,1,1,2,2,2,1,1,2,2], [1,2,2,2,2,2,1,1,1,0]);
  expect r18 == 3, "Test 18 failed";

  // Test 19
  var r19 := Tram(10, [0,0,0,0,0,0,0,0,0,0], [0,0,0,0,0,0,0,0,0,0]);
  expect r19 == 0, "Test 19 failed";

  // Test 20
  var r20 := Tram(10, [0,1000,1000,1000,1000,1000,1000,1000,1000,1000], [1000,1000,1000,1000,1000,1000,1000,1000,1000,0]);
  expect r20 == 1000, "Test 20 failed";

  print "All tests passed\n";
}
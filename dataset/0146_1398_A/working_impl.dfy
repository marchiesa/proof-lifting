method BadTriangle(a: seq<int>) returns (result: (int, int, int), found: bool)
{
  result := (0, 0, 0);
  found := false;
  var n := |a|;

  var x := a[0] + a[1] - a[n - 1];
  var y := a[0] - a[1] + a[n - 1];
  var z := -a[0] + a[1] + a[n - 1];
  if x <= 0 || y <= 0 || z <= 0 {
    result := (1, 2, n);
    found := true;
    return;
  }

  x := a[0] + a[n - 1] - a[n - 2];
  y := a[0] - a[n - 1] + a[n - 2];
  z := -a[0] + a[n - 1] + a[n - 2];
  if x <= 0 || y <= 0 || z <= 0 {
    result := (1, n - 1, n);
    found := true;
    return;
  }

  x := a[0] + a[1] - a[2];
  y := a[0] - a[1] + a[2];
  z := -a[0] + a[1] + a[2];
  if x <= 0 || y <= 0 || z <= 0 {
    result := (1, 2, 3);
    found := true;
    return;
  }

  x := a[n - 3] + a[n - 2] - a[n - 1];
  y := a[n - 3] - a[n - 2] + a[n - 1];
  z := -a[n - 3] + a[n - 2] + a[n - 1];
  if x <= 0 || y <= 0 || z <= 0 {
    result := (n - 2, n - 1, n);
    found := true;
    return;
  }
}

method Main()
{
  // Test 1a: [4, 6, 11, 11, 15, 18, 20] -> (1, 2, 7)
  var r1, f1 := BadTriangle([4, 6, 11, 11, 15, 18, 20]);
  expect f1 == true;
  expect r1 == (1, 2, 7);

  // Test 1b: [10, 10, 10, 11] -> -1
  var r2, f2 := BadTriangle([10, 10, 10, 11]);
  expect f2 == false;

  // Test 1c: [1, 1, 1000000000] -> (1, 2, 3)
  var r3, f3 := BadTriangle([1, 1, 1000000000]);
  expect f3 == true;
  expect r3 == (1, 2, 3);

  // Test 2: [78788, 78788, 100000] -> -1
  var r4, f4 := BadTriangle([78788, 78788, 100000]);
  expect f4 == false;

  // Test 3: [78788, 78788, 157577] -> (1, 2, 3)
  var r5, f5 := BadTriangle([78788, 78788, 157577]);
  expect f5 == true;
  expect r5 == (1, 2, 3);

  // Test 4: [1, 7, 7, 7, 7, 9, 9, 9, 9, 9] -> (1, 2, 10)
  var r6, f6 := BadTriangle([1, 7, 7, 7, 7, 9, 9, 9, 9, 9]);
  expect f6 == true;
  expect r6 == (1, 2, 10);

  // Test 5: [1, 1, 1, 2, 2, 3] -> (1, 2, 6)
  var r7, f7 := BadTriangle([1, 1, 1, 2, 2, 3]);
  expect f7 == true;
  expect r7 == (1, 2, 6);

  // Test 6: [5623, 5624, 10000000] -> (1, 2, 3)
  var r8, f8 := BadTriangle([5623, 5624, 10000000]);
  expect f8 == true;
  expect r8 == (1, 2, 3);

  // Test 7: [5739271, 5739272, 20000000] -> (1, 2, 3)
  var r9, f9 := BadTriangle([5739271, 5739272, 20000000]);
  expect f9 == true;
  expect r9 == (1, 2, 3);

  // Test 8: [1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 4] -> (1, 2, 14)
  var r10, f10 := BadTriangle([1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 4]);
  expect f10 == true;
  expect r10 == (1, 2, 14);

  // Test 9: [1, 65535, 10000000] -> (1, 2, 3)
  var r11, f11 := BadTriangle([1, 65535, 10000000]);
  expect f11 == true;
  expect r11 == (1, 2, 3);

  // Test 10: [21, 78868, 80000] -> (1, 2, 3)
  var r12, f12 := BadTriangle([21, 78868, 80000]);
  expect f12 == true;
  expect r12 == (1, 2, 3);

  // Test 11: [3, 4, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 32, 36, 39] -> (1, 2, 15)
  var r13, f13 := BadTriangle([3, 4, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 32, 36, 39]);
  expect f13 == true;
  expect r13 == (1, 2, 15);

  print "All tests passed\n";
}
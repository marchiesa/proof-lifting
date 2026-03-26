method Barrels(a: seq<int>, k: int) returns (diff: int)
{
  var n := |a|;
  if n == 0 {
    return 0;
  }

  // Copy sequence to mutable array
  var arr := new int[n];
  var i := 0;
  while i < n {
    arr[i] := a[i];
    i := i + 1;
  }

  // Sort ascending (selection sort)
  i := 0;
  while i < n {
    var j := i + 1;
    while j < n {
      if arr[j] < arr[i] {
        var tmp := arr[i];
        arr[i] := arr[j];
        arr[j] := tmp;
      }
      j := j + 1;
    }
    i := i + 1;
  }

  // Merge top k+1 elements into the largest
  i := 0;
  while i < k {
    var idx := n - 2 - i;
    if idx < 0 {
      break;
    }
    arr[n - 1] := arr[n - 1] + arr[idx];
    arr[idx] := 0;
    i := i + 1;
  }

  // Find max and min
  var maxVal := arr[0];
  var minVal := arr[0];
  i := 1;
  while i < n {
    if arr[i] > maxVal {
      maxVal := arr[i];
    }
    if arr[i] < minVal {
      minVal := arr[i];
    }
    i := i + 1;
  }

  return maxVal - minVal;
}

method Main()
{
  // Test 1a: [5,5,5,5], k=1 → 10
  var r1a := Barrels([5, 5, 5, 5], 1);
  expect r1a == 10, "Test 1a failed";

  // Test 1b: [0,0,0], k=2 → 0
  var r1b := Barrels([0, 0, 0], 2);
  expect r1b == 0, "Test 1b failed";

  // Test 2: [3,7,1,9,5], k=2 → 21
  var r2 := Barrels([3, 7, 1, 9, 5], 2);
  expect r2 == 21, "Test 2 failed";

  // Test 3: [0,0,0], k=1 → 0
  var r3 := Barrels([0, 0, 0], 1);
  expect r3 == 0, "Test 3 failed";

  // Test 4: [10,20], k=1 → 30
  var r4 := Barrels([10, 20], 1);
  expect r4 == 30, "Test 4 failed";

  // Test 5: [5,5,5,5], k=3 → 20
  var r5 := Barrels([5, 5, 5, 5], 3);
  expect r5 == 20, "Test 5 failed";

  // Test 6: [1,2,3,4,5,6], k=2 → 15
  var r6 := Barrels([1, 2, 3, 4, 5, 6], 2);
  expect r6 == 15, "Test 6 failed";

  // Test 7: [50,0,50], k=1 → 100
  var r7 := Barrels([50, 0, 50], 1);
  expect r7 == 100, "Test 7 failed";

  // Test 8: [42], k=0 → 0
  var r8 := Barrels([42], 0);
  expect r8 == 0, "Test 8 failed";

  // Test 9a: [7,3], k=1 → 10
  var r9a := Barrels([7, 3], 1);
  expect r9a == 10, "Test 9a failed";

  // Test 9b: [10,20,30,40], k=2 → 90
  var r9b := Barrels([10, 20, 30, 40], 2);
  expect r9b == 90, "Test 9b failed";

  // Test 9c: [0,5,0], k=1 → 5
  var r9c := Barrels([0, 5, 0], 1);
  expect r9c == 5, "Test 9c failed";

  // Test 10: [0,0,0,0,0,0,0], k=3 → 0
  var r10 := Barrels([0, 0, 0, 0, 0, 0, 0], 3);
  expect r10 == 0, "Test 10 failed";

  // Test 11: [8,3,12,1,6], k=4 → 30
  var r11 := Barrels([8, 3, 12, 1, 6], 4);
  expect r11 == 30, "Test 11 failed";

  print "All tests passed\n";
}
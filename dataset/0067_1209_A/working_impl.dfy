method PaintTheNumbers(a: seq<int>) returns (colors: int)
{
  var n := |a|;
  if n == 0 {
    return 0;
  }

  var arr := new int[n];
  var i := 0;
  while i < n {
    arr[i] := a[i];
    i := i + 1;
  }

  // Selection sort
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

  // For each remaining non-zero element, zero out all its multiples
  var ans := 0;
  i := 0;
  while i < n {
    if arr[i] != 0 {
      var x := arr[i];
      var j := i;
      while j < n {
        if arr[j] % x == 0 {
          arr[j] := 0;
        }
        j := j + 1;
      }
      ans := ans + 1;
    }
    i := i + 1;
  }

  return ans;
}

method Main()
{
  var result: int;

  // Test 1
  result := PaintTheNumbers([10, 2, 3, 5, 4, 2]);
  expect result == 3, "Test 1 failed";

  // Test 2
  result := PaintTheNumbers([100, 100, 100, 100]);
  expect result == 1, "Test 2 failed";

  // Test 3
  result := PaintTheNumbers([7, 6, 5, 4, 3, 2, 2, 3]);
  expect result == 4, "Test 3 failed";

  // Test 4
  result := PaintTheNumbers([1]);
  expect result == 1, "Test 4 failed";

  // Test 5
  result := PaintTheNumbers([100]);
  expect result == 1, "Test 5 failed";

  // Test 6
  result := PaintTheNumbers([2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97, 2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97, 2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97, 2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97]);
  expect result == 25, "Test 6 failed";

  // Test 7
  result := PaintTheNumbers([17, 23, 71, 25, 50, 71, 85, 46, 78, 72, 89, 26, 23, 70, 40, 59, 23, 43, 86, 81, 70, 89, 92, 98, 85, 88, 16, 10, 26, 91, 61, 58, 23, 13, 75, 39, 48, 15, 73, 79, 59, 29, 48, 32, 45, 44, 25, 37, 58, 54, 45, 67, 27, 77, 20, 64, 95, 41, 80, 53, 69, 24, 38, 97, 59, 94, 50, 88, 92, 47, 95, 31, 66, 48, 48, 56, 37, 76, 42, 74, 55, 34, 43, 79, 65, 82, 70, 52, 48, 56, 36, 17, 14, 65, 77, 81, 88, 18, 33, 40]);
  expect result == 32, "Test 7 failed";

  // Test 8
  result := PaintTheNumbers([89, 38, 63, 73, 77, 4, 99, 74, 30, 5, 69, 57, 97, 37, 88, 71, 36, 59, 19, 63, 46, 20, 33, 58, 61, 98, 100, 31, 33, 53, 99, 96, 34, 17, 44, 95, 54, 52, 22, 77, 67, 88, 20, 88, 26, 43, 12, 23, 96, 94, 14, 7, 57, 86, 56, 54, 32, 8, 3, 43, 97, 56, 74, 22, 5, 100, 12, 60, 93, 12, 44, 68, 31, 63, 7, 71, 21, 29, 19, 38, 50, 47, 97, 43, 50, 59, 88, 40, 51, 61, 20, 68, 32, 66, 70, 48, 19, 55, 91, 53]);
  expect result == 22, "Test 8 failed";

  // Test 9
  result := PaintTheNumbers([9, 9, 72, 55, 14, 8, 55, 58, 35, 67, 3, 18, 73, 92, 41, 49, 15, 60, 18, 66, 9, 26, 97, 47, 43, 88, 71, 97, 19, 34, 48, 96, 79, 53, 8, 24, 69, 49, 12, 23, 77, 12, 21, 88, 66, 9, 29, 13, 61, 69, 54, 77, 41, 13, 4, 68, 37, 74, 7, 6, 29, 76, 55, 72, 89, 4, 78, 27, 29, 82, 18, 83, 12, 4, 32, 69, 89, 85, 66, 13, 92, 54, 38, 5, 26, 56, 17, 55, 29, 4, 17, 39, 29, 94, 3, 67, 85, 98, 21, 14]);
  expect result == 22, "Test 9 failed";

  // Test 10
  result := PaintTheNumbers([83, 74, 53, 90, 85, 65, 55, 74, 86, 64, 69, 70, 66, 57, 93, 90, 97, 66, 62, 52, 76, 80, 70, 65, 79, 59, 88, 65, 76, 70, 94, 57, 53, 83, 91, 69, 59, 80, 82, 53, 97, 91, 75, 74, 77, 70, 51, 58, 56, 79, 72, 79, 60, 91, 60, 84, 75, 92, 88, 93, 96, 100, 56, 77, 55, 56, 69, 80, 100, 78, 68, 69, 90, 99, 97, 62, 85, 97, 71, 52, 60, 83, 85, 89, 96, 98, 59, 96, 85, 98, 51, 90, 90, 71, 97, 91, 94, 64, 57, 52]);
  expect result == 42, "Test 10 failed";

  // Test 11
  result := PaintTheNumbers([94, 83, 55, 57, 63, 89, 73, 59, 75, 97, 77, 54, 77, 81, 70, 81, 99, 52, 88, 76, 98, 88, 79, 67, 76, 80, 89, 50, 60, 60, 53, 83, 96, 87, 75, 99, 61, 91, 75, 85, 88, 80, 90, 54, 84, 88, 98, 93, 69, 97, 93, 54, 83, 59, 57, 92, 88, 78, 53, 55, 99, 63, 60, 70, 61, 52, 60, 55, 100, 85, 80, 58, 53, 97, 59, 61, 50, 90, 75, 85, 86, 63, 91, 96, 67, 68, 86, 96, 79, 98, 51, 83, 82, 92, 65, 100, 76, 83, 57, 100]);
  expect result == 42, "Test 11 failed";

  // Test 12
  result := PaintTheNumbers([70, 89, 84, 63, 91, 63, 75, 56, 87, 98, 93, 58, 95, 67, 57, 90, 56, 100, 84, 82, 80, 64, 71, 58, 67, 62, 52, 81, 92, 74, 79, 83, 100, 72, 70, 61, 97, 86, 91, 93, 62, 86, 88, 66, 55, 59, 65, 59, 72, 80, 68, 95, 53, 82, 54, 85, 81, 85, 52, 65, 96, 94, 66, 74, 68, 64, 73, 99, 97, 99, 78, 69, 79, 90, 54, 51, 87, 96, 77, 78, 77, 76, 98, 53, 71, 76, 55, 61, 89, 94, 88, 57, 83, 51, 69, 60, 75, 60, 92, 73]);
  expect result == 50, "Test 12 failed";

  // Test 13
  result := PaintTheNumbers([7, 70, 8, 9, 8, 9, 35, 1, 99, 27]);
  expect result == 1, "Test 13 failed";

  // Test 14
  result := PaintTheNumbers([40, 80, 40, 40, 40]);
  expect result == 1, "Test 14 failed";

  // Test 15
  result := PaintTheNumbers([13, 63, 82, 53, 83, 30, 7, 8, 21, 61, 74, 41, 11, 54, 71, 53, 66]);
  expect result == 12, "Test 15 failed";

  // Test 16
  result := PaintTheNumbers([8, 5, 5, 10, 8, 10, 8, 9, 7, 9]);
  expect result == 4, "Test 16 failed";

  // Test 17
  result := PaintTheNumbers([6, 8, 14, 8, 9, 4, 7, 9, 7, 6, 9, 10, 14, 14, 11, 7, 12, 6, 11, 6]);
  expect result == 6, "Test 17 failed";

  // Test 18
  result := PaintTheNumbers([5, 4, 2, 6, 9, 8, 2, 8, 6, 4, 4, 6, 5, 10, 6]);
  expect result == 3, "Test 18 failed";

  // Test 19
  result := PaintTheNumbers([2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97, 1]);
  expect result == 1, "Test 19 failed";

  // Test 20
  result := PaintTheNumbers([1, 1]);
  expect result == 1, "Test 20 failed";

  print "All tests passed\n";
}
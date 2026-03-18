method MeanInequality(a: seq<int>, n: int) returns (b: seq<int>)
{
  var arr := new int[|a|];
  var k := 0;
  while k < |a| {
    arr[k] := a[k];
    k := k + 1;
  }

  // Selection sort
  var i := 0;
  while i < arr.Length {
    var minIdx := i;
    var j := i + 1;
    while j < arr.Length {
      if arr[j] < arr[minIdx] {
        minIdx := j;
      }
      j := j + 1;
    }
    var tmp := arr[i];
    arr[i] := arr[minIdx];
    arr[minIdx] := tmp;
    i := i + 1;
  }

  // Swap first and last
  if arr.Length > 0 {
    var tmp := arr[0];
    arr[0] := arr[arr.Length - 1];
    arr[arr.Length - 1] := tmp;
  }

  // Swap adjacent pairs
  i := 1;
  while i < n - 1 {
    var tmp := arr[i * 2];
    arr[i * 2] := arr[i * 2 + 1];
    arr[i * 2 + 1] := tmp;
    i := i + 1;
  }

  // Convert array back to seq
  b := [];
  k := 0;
  while k < arr.Length {
    b := b + [arr[k]];
    k := k + 1;
  }
}

method Main()
{
  // Test 1, case 1
  var r1a := MeanInequality([1, 2, 3, 4, 5, 6], 3);
  expect r1a == [6, 2, 4, 3, 5, 1], "Test 1.1 failed";

  // Test 1, case 2
  var r1b := MeanInequality([123, 456, 789, 10], 2);
  expect r1b == [789, 123, 456, 10], "Test 1.2 failed";

  // Test 1, case 3
  var r1c := MeanInequality([6, 9], 1);
  expect r1c == [9, 6], "Test 1.3 failed";

  // Test 2
  var r2 := MeanInequality([420, 69], 1);
  expect r2 == [420, 69], "Test 2 failed";

  // Test 3
  var r3 := MeanInequality([1, 2], 1);
  expect r3 == [2, 1], "Test 3 failed";

  // Test 4
  var r4 := MeanInequality([1, 2, 3, 4], 2);
  expect r4 == [4, 2, 3, 1], "Test 4 failed";

  // Test 5
  var r5 := MeanInequality([1, 2, 3, 4, 5, 6], 3);
  expect r5 == [6, 2, 4, 3, 5, 1], "Test 5 failed";

  // Test 6
  var r6 := MeanInequality([10, 20], 1);
  expect r6 == [20, 10], "Test 6 failed";

  // Test 7
  var r7 := MeanInequality([1, 3, 5, 7, 9, 11, 13, 15], 4);
  expect r7 == [15, 3, 7, 5, 11, 9, 13, 1], "Test 7 failed";

  // Test 8, case 1
  var r8a := MeanInequality([5, 8], 1);
  expect r8a == [8, 5], "Test 8.1 failed";

  // Test 8, case 2
  var r8b := MeanInequality([10, 20, 30, 40], 2);
  expect r8b == [40, 20, 30, 10], "Test 8.2 failed";

  // Test 9
  var r9 := MeanInequality([2, 4, 6, 8, 10, 12, 14, 16, 18, 20], 5);
  expect r9 == [20, 4, 8, 6, 12, 10, 16, 14, 18, 2], "Test 9 failed";

  // Test 10, case 1
  var r10a := MeanInequality([1, 50], 1);
  expect r10a == [50, 1], "Test 10.1 failed";

  // Test 10, case 2
  var r10b := MeanInequality([25, 30], 1);
  expect r10b == [30, 25], "Test 10.2 failed";

  // Test 10, case 3
  var r10c := MeanInequality([3, 7], 1);
  expect r10c == [7, 3], "Test 10.3 failed";

  // Test 11
  var r11 := MeanInequality([10, 20, 30, 40, 50, 49], 3);
  expect r11 == [50, 20, 40, 30, 49, 10], "Test 11 failed";

  // Test 12
  var r12 := MeanInequality([1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50], 25);
  expect r12 == [50, 2, 4, 3, 6, 5, 8, 7, 10, 9, 12, 11, 14, 13, 16, 15, 18, 17, 20, 19, 22, 21, 24, 23, 26, 25, 28, 27, 30, 29, 32, 31, 34, 33, 36, 35, 38, 37, 40, 39, 42, 41, 44, 43, 46, 45, 48, 47, 49, 1], "Test 12 failed";

  print "All tests passed\n";
}
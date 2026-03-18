method ChooseTwoNumbers(A: seq<int>, B: seq<int>) returns (a: int, b: int)
{
  var sortedA := A;
  var sortedB := B;

  var i := 0;
  while i < |sortedA|
  {
    var j := i + 1;
    while j < |sortedA|
    {
      if sortedA[j] < sortedA[i]
      {
        var tmp := sortedA[i];
        sortedA := sortedA[i := sortedA[j]];
        sortedA := sortedA[j := tmp];
      }
      j := j + 1;
    }
    i := i + 1;
  }

  i := 0;
  while i < |sortedB|
  {
    var j := i + 1;
    while j < |sortedB|
    {
      if sortedB[j] < sortedB[i]
      {
        var tmp := sortedB[i];
        sortedB := sortedB[i := sortedB[j]];
        sortedB := sortedB[j := tmp];
      }
      j := j + 1;
    }
    i := i + 1;
  }

  a := sortedA[|sortedA| - 1];
  b := sortedB[|sortedB| - 1];
}

method Main()
{
  // Test 1
  var a1, b1 := ChooseTwoNumbers([20], [10, 20]);
  expect a1 == 20 && b1 == 20, "Test 1 failed";

  // Test 2
  var a2, b2 := ChooseTwoNumbers([3, 2, 2], [1, 5, 7, 7, 9]);
  expect a2 == 3 && b2 == 9, "Test 2 failed";

  // Test 3
  var a3, b3 := ChooseTwoNumbers([1, 3, 5, 7], [7, 5, 3, 1]);
  expect a3 == 7 && b3 == 7, "Test 3 failed";

  // Test 4
  var a4, b4 := ChooseTwoNumbers([1], [1, 2, 3, 4, 5, 6, 7, 8, 9, 10]);
  expect a4 == 1 && b4 == 10, "Test 4 failed";

  // Test 5
  var a5, b5 := ChooseTwoNumbers([148], [40]);
  expect a5 == 148 && b5 == 40, "Test 5 failed";

  // Test 6
  var a6, b6 := ChooseTwoNumbers([77, 112, 81, 91], [183, 174, 187, 111, 121, 21, 129, 28]);
  expect a6 == 112 && b6 == 187, "Test 6 failed";

  // Test 7
  var a7, b7 := ChooseTwoNumbers([80, 141, 15, 177, 191, 182, 115, 183, 36, 3], [129, 114, 183, 94, 169, 16, 18, 104, 49, 146, 68, 157, 33, 38, 10, 77, 112, 47, 73, 37]);
  expect a7 == 191 && b7 == 183, "Test 7 failed";

  // Test 8
  var a8, b8 := ChooseTwoNumbers([199, 34, 116, 194, 65, 130, 88, 7, 29, 130, 11, 142, 186, 98, 182, 87, 170, 4, 37, 17], [116, 2, 185, 117, 66, 158, 78, 120, 196, 175, 101, 117, 52, 27, 155, 153, 96, 200, 81, 38, 36, 89, 154, 8, 77, 7, 31, 163, 174, 189, 126, 155, 111, 115, 199, 2, 25, 5, 150, 5]);
  expect a8 == 199 && b8 == 200, "Test 8 failed";

  // Test 9
  var a9, b9 := ChooseTwoNumbers([197, 90, 23, 11, 63, 198, 24, 132, 68, 58, 195, 100, 101, 120, 96, 77, 132, 155, 62, 197, 170, 117, 189, 160, 194, 106, 172, 124, 180, 75, 124, 51, 51, 93, 186, 93, 79, 111, 161, 67, 84, 183, 150, 125, 25, 46, 106, 29, 170, 175, 4, 122], [95, 28, 20, 190, 75, 89, 193, 152, 53, 79, 100, 3, 154, 42, 67, 5, 137, 60]);
  expect a9 == 198 && b9 == 193, "Test 9 failed";

  // Test 10
  var a10, b10 := ChooseTwoNumbers([101], [101]);
  expect a10 == 101 && b10 == 101, "Test 10 failed";

  // Test 11
  var a11, b11 := ChooseTwoNumbers([1, 4], [5, 1, 1]);
  expect a11 == 4 && b11 == 5, "Test 11 failed";

  // Test 12
  var a12, b12 := ChooseTwoNumbers([1], [2, 1]);
  expect a12 == 1 && b12 == 2, "Test 12 failed";

  // Test 13
  var a13, b13 := ChooseTwoNumbers([1, 2, 3, 4, 5], [1]);
  expect a13 == 5 && b13 == 1, "Test 13 failed";

  // Test 14
  var a14, b14 := ChooseTwoNumbers([200], [200]);
  expect a14 == 200 && b14 == 200, "Test 14 failed";

  // Test 15
  var a15, b15 := ChooseTwoNumbers([1, 2, 3], [1]);
  expect a15 == 3 && b15 == 1, "Test 15 failed";

  // Test 16
  var a16, b16 := ChooseTwoNumbers([1], [1, 2, 1]);
  expect a16 == 1 && b16 == 2, "Test 16 failed";

  // Test 17
  var a17, b17 := ChooseTwoNumbers([1], [3, 2, 1]);
  expect a17 == 1 && b17 == 3, "Test 17 failed";

  // Test 18
  var a18, b18 := ChooseTwoNumbers([1, 2, 3, 4, 5], [7, 1, 2]);
  expect a18 == 5 && b18 == 7, "Test 18 failed";

  // Test 19
  var a19, b19 := ChooseTwoNumbers([1, 2, 3], [2, 3, 4, 1]);
  expect a19 == 3 && b19 == 4, "Test 19 failed";

  // Test 20
  var a20, b20 := ChooseTwoNumbers([1, 2, 3], [1, 1, 4, 1]);
  expect a20 == 3 && b20 == 4, "Test 20 failed";

  print "All tests passed\n";
}
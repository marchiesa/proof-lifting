method TitForTat(a: seq<int>, k: int) returns (result: seq<int>)
{
  var A := a;
  var remaining := k;
  var n := |A|;
  var i := 0;
  while i < n - 1 && remaining > 0
  {
    var val := A[i];
    if remaining >= val {
      A := A[i := 0];
      remaining := remaining - val;
      A := A[n - 1 := A[n - 1] + val];
    } else {
      A := A[i := A[i] - remaining];
      A := A[n - 1 := A[n - 1] + remaining];
      remaining := 0;
    }
    i := i + 1;
  }
  result := A;
}

method Main()
{
  // Test 1, Case 1
  var r1 := TitForTat([3, 1, 4], 1);
  expect r1 == [2, 1, 5], "Test 1.1 failed";

  // Test 1, Case 2
  var r2 := TitForTat([1, 0], 10);
  expect r2 == [0, 1], "Test 1.2 failed";

  // Test 2
  var r3 := TitForTat([1, 8, 9], 1);
  expect r3 == [0, 8, 10], "Test 2 failed";

  // Test 3
  var r4 := TitForTat([3, 1, 9], 1);
  expect r4 == [2, 1, 10], "Test 3 failed";

  // Test 4
  var r5 := TitForTat([1, 0, 1], 1);
  expect r5 == [0, 0, 2], "Test 4 failed";

  // Test 5
  var r6 := TitForTat([0, 0], 1);
  expect r6 == [0, 0], "Test 5 failed";

  // Test 6
  var r7 := TitForTat([5, 5, 5], 3);
  expect r7 == [2, 5, 8], "Test 6 failed";

  // Test 7
  var r8 := TitForTat([1, 2, 3, 4], 2);
  expect r8 == [0, 1, 3, 6], "Test 7 failed";

  // Test 8
  var r9 := TitForTat([10, 0, 10, 0, 10], 10);
  expect r9 == [0, 0, 10, 0, 20], "Test 8 failed";

  // Test 9
  var r10 := TitForTat([50, 50], 50);
  expect r10 == [0, 100], "Test 9 failed";

  // Test 10
  var r11 := TitForTat([0, 0, 7], 1);
  expect r11 == [0, 0, 7], "Test 10 failed";

  // Test 11
  var r12 := TitForTat([3, 1, 4, 1, 5, 9], 5);
  expect r12 == [0, 0, 3, 1, 5, 14], "Test 11 failed";

  // Test 12
  var r13 := TitForTat([1, 2, 3, 4, 5, 6, 7, 8, 9, 10], 20);
  expect r13 == [0, 0, 0, 0, 0, 1, 7, 8, 9, 30], "Test 12 failed";

  // Test 13, Case 1
  var r14 := TitForTat([5, 3], 1);
  expect r14 == [4, 4], "Test 13.1 failed";

  // Test 13, Case 2
  var r15 := TitForTat([0, 0, 1, 2], 3);
  expect r15 == [0, 0, 0, 3], "Test 13.2 failed";

  // Test 13, Case 3
  var r16 := TitForTat([10, 10, 10], 2);
  expect r16 == [8, 10, 12], "Test 13.3 failed";

  print "All tests passed\n";
}
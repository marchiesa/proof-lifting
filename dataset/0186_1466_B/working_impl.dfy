method MaxDiversity(notes: seq<int>) returns (diversity: int)
{
  var n := |notes|;
  if n == 0 {
    return 0;
  }
  var arr := new int[n];
  var k := 0;
  while k < n {
    arr[k] := notes[k];
    k := k + 1;
  }
  var cnt := 1;
  arr[n - 1] := arr[n - 1] + 1;
  var i := n - 2;
  while i >= 0 {
    if arr[i] == arr[i + 1] {
      // same value, skip
    } else if arr[i] + 1 == arr[i + 1] {
      cnt := cnt + 1;
    } else {
      arr[i] := arr[i] + 1;
      cnt := cnt + 1;
    }
    i := i - 1;
  }
  return cnt;
}

method Main()
{
  var d: int;

  // Test 1
  d := MaxDiversity([1, 2, 2, 2, 5, 6]);
  expect d == 5, "Test 1.1 failed";

  d := MaxDiversity([4, 4]);
  expect d == 2, "Test 1.2 failed";

  d := MaxDiversity([1, 1, 3, 4, 4, 5]);
  expect d == 6, "Test 1.3 failed";

  d := MaxDiversity([1]);
  expect d == 1, "Test 1.4 failed";

  d := MaxDiversity([1, 1, 1, 2, 2, 2]);
  expect d == 3, "Test 1.5 failed";

  // Test 2
  d := MaxDiversity([1, 2, 3, 4]);
  expect d == 4, "Test 2.1 failed";

  d := MaxDiversity([1, 1, 1]);
  expect d == 2, "Test 2.2 failed";

  d := MaxDiversity([2, 2, 4, 4, 6]);
  expect d == 5, "Test 2.3 failed";

  // Test 3
  d := MaxDiversity([7]);
  expect d == 1, "Test 3.1 failed";

  // Test 4
  d := MaxDiversity([1, 1, 2, 3, 5, 5]);
  expect d == 6, "Test 4.1 failed";

  d := MaxDiversity([1, 1, 1, 1]);
  expect d == 2, "Test 4.2 failed";

  // Test 5
  d := MaxDiversity([1, 1, 2, 3, 3, 4, 5, 5, 6, 7]);
  expect d == 8, "Test 5.1 failed";

  // Test 6
  d := MaxDiversity([3, 3]);
  expect d == 2, "Test 6.1 failed";

  d := MaxDiversity([1, 2, 3]);
  expect d == 3, "Test 6.2 failed";

  d := MaxDiversity([1, 1, 1, 1, 1]);
  expect d == 2, "Test 6.3 failed";

  d := MaxDiversity([2, 4, 6, 8]);
  expect d == 4, "Test 6.4 failed";

  // Test 7
  d := MaxDiversity([1, 1, 1, 1, 1, 1, 1]);
  expect d == 2, "Test 7.1 failed";

  // Test 8
  d := MaxDiversity([1, 2, 2, 3, 4]);
  expect d == 5, "Test 8.1 failed";

  d := MaxDiversity([50]);
  expect d == 1, "Test 8.2 failed";

  d := MaxDiversity([1, 3, 3, 5, 5, 5]);
  expect d == 5, "Test 8.3 failed";

  // Test 9
  d := MaxDiversity([1, 1, 2, 2, 3, 3, 4, 4]);
  expect d == 5, "Test 9.1 failed";

  d := MaxDiversity([1, 1, 2]);
  expect d == 3, "Test 9.2 failed";

  // Test 10
  d := MaxDiversity([1, 2, 3, 4, 5, 6, 7, 8, 9, 10]);
  expect d == 10, "Test 10.1 failed";

  // Test 11
  d := MaxDiversity([1, 2]);
  expect d == 2, "Test 11.1 failed";

  d := MaxDiversity([1, 1]);
  expect d == 2, "Test 11.2 failed";

  d := MaxDiversity([2, 2, 2]);
  expect d == 2, "Test 11.3 failed";

  d := MaxDiversity([1, 1, 3, 3]);
  expect d == 4, "Test 11.4 failed";

  d := MaxDiversity([1]);
  expect d == 1, "Test 11.5 failed";

  print "All tests passed\n";
}
method GameOfLife(cells: seq<int>, m: int) returns (result: seq<int>)
{
  var n := |cells|;
  if n == 0 {
    result := [];
    return;
  }
  var INF := 10000000000;

  // Compute left: index of nearest 1 at or to the left of each position
  var left: seq<int> := [];
  var last1 := -INF;
  var i := 0;
  while i < n
  {
    if cells[i] == 1 {
      last1 := i;
    }
    left := left + [last1];
    i := i + 1;
  }

  // Compute right: index of nearest 1 at or to the right of each position
  var right: seq<int> := [];
  i := 0;
  while i < n
  {
    right := right + [INF];
    i := i + 1;
  }
  last1 := INF;
  i := n - 1;
  while i >= 0
  {
    if cells[i] == 1 {
      last1 := i;
    }
    right := right[i := last1];
    i := i - 1;
  }

  // Compute result
  var ans: seq<int> := [];
  i := 0;
  while i < n
  {
    if left[i] == i {
      ans := ans + [1];
    } else if (i - left[i] <= m || right[i] - i <= m) && i - left[i] != right[i] - i {
      ans := ans + [1];
    } else {
      ans := ans + [0];
    }
    i := i + 1;
  }
  result := ans;
}

method Main()
{
  // Test 1.1: n=11, m=3
  var r1 := GameOfLife([0,1,0,0,0,0,0,0,0,0,1], 3);
  expect r1 == [1,1,1,1,1,0,0,1,1,1,1], "Test 1.1 failed";

  // Test 1.2: n=10, m=2
  var r2 := GameOfLife([0,1,1,0,1,0,0,1,0,1], 2);
  expect r2 == [1,1,1,0,1,1,1,1,0,1], "Test 1.2 failed";

  // Test 1.3: n=5, m=2
  var r3 := GameOfLife([1,0,1,0,1], 2);
  expect r3 == [1,0,1,0,1], "Test 1.3 failed";

  // Test 1.4: n=3, m=100
  var r4 := GameOfLife([0,0,0], 100);
  expect r4 == [0,0,0], "Test 1.4 failed";

  // Test 2: n=11, m=1
  var r5 := GameOfLife([1,0,0,0,0,1,0,0,0,0,1], 1);
  expect r5 == [1,1,0,0,1,1,1,0,0,1,1], "Test 2 failed";

  // Test 3: n=4, m=1000000000
  var r6 := GameOfLife([1,0,1,0], 1000000000);
  expect r6 == [1,0,1,1], "Test 3 failed";

  // Test 4: n=5, m=42069
  var r7 := GameOfLife([1,1,0,1,1], 42069);
  expect r7 == [1,1,0,1,1], "Test 4 failed";

  // Test 5: n=3, m=1000000000
  var r8 := GameOfLife([1,0,1], 1000000000);
  expect r8 == [1,0,1], "Test 5 failed";

  // Test 6: n=5, m=1000000000
  var r9 := GameOfLife([1,1,0,1,1], 1000000000);
  expect r9 == [1,1,0,1,1], "Test 6 failed";

  // Test 7: n=11, m=1000000000
  var r10 := GameOfLife([1,1,1,1,1,1,1,1,1,0,1], 1000000000);
  expect r10 == [1,1,1,1,1,1,1,1,1,0,1], "Test 7 failed";

  // Test 8.1: n=3, m=1
  var r11 := GameOfLife([1,1,1], 1);
  expect r11 == [1,1,1], "Test 8.1 failed";

  // Test 8.2: n=2, m=2
  var r12 := GameOfLife([0,0], 2);
  expect r12 == [0,0], "Test 8.2 failed";

  // Test 9.1: n=10, m=1
  var r13 := GameOfLife([1,1,1,1,1,1,1,1,1,1], 1);
  expect r13 == [1,1,1,1,1,1,1,1,1,1], "Test 9.1 failed";

  // Test 9.2: n=9, m=4
  var r14 := GameOfLife([0,0,0,0,0,0,0,0,0], 4);
  expect r14 == [0,0,0,0,0,0,0,0,0], "Test 9.2 failed";

  // Test 9.3: n=9, m=4
  var r15 := GameOfLife([0,0,0,0,0,0,0,0,0], 4);
  expect r15 == [0,0,0,0,0,0,0,0,0], "Test 9.3 failed";

  // Test 9.4: n=9, m=4
  var r16 := GameOfLife([0,0,0,0,0,0,0,0,0], 4);
  expect r16 == [0,0,0,0,0,0,0,0,0], "Test 9.4 failed";

  print "All tests passed\n";
}
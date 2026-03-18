method CircleColoring(n: int, a: seq<int>, b: seq<int>, c: seq<int>) returns (p: seq<int>)
{
  var out := new int[n];
  var i := 0;
  while i < n {
    out[i] := -1;
    i := i + 1;
  }
  i := 0;
  while i < n {
    var prev := (i - 1 + n) % n;
    var next := (i + 1) % n;
    if a[i] != out[prev] && a[i] != out[next] {
      out[i] := a[i];
    }
    if b[i] != out[prev] && b[i] != out[next] {
      out[i] := b[i];
    }
    if c[i] != out[prev] && c[i] != out[next] {
      out[i] := c[i];
    }
    i := i + 1;
  }
  p := out[..];
}

method Main()
{
  var p: seq<int>;

  // Test 1, Case 1: n=3
  p := CircleColoring(3, [1,1,1], [2,2,2], [3,3,3]);
  expect p == [3,2,1], "Test 1.1 failed";

  // Test 1, Case 2: n=4
  p := CircleColoring(4, [1,2,1,2], [2,1,2,1], [3,4,3,4]);
  expect p == [3,4,3,4], "Test 1.2 failed";

  // Test 1, Case 3: n=7
  p := CircleColoring(7, [1,3,3,1,1,1,1], [2,4,4,3,2,2,4], [4,2,2,2,4,4,2]);
  expect p == [4,2,4,2,4,2,1], "Test 1.3 failed";

  // Test 1, Case 4: n=3
  p := CircleColoring(3, [1,2,1], [2,3,3], [3,1,2]);
  expect p == [3,1,2], "Test 1.4 failed";

  // Test 1, Case 5: n=10
  p := CircleColoring(10, [1,1,1,2,2,2,3,3,3,1], [2,2,2,3,3,3,1,1,1,2], [3,3,3,1,1,1,2,2,2,3]);
  expect p == [3,2,3,1,3,1,2,1,2,1], "Test 1.5 failed";

  // Test 2: n=3
  p := CircleColoring(3, [1,2,3], [2,3,1], [3,1,2]);
  expect p == [3,1,2], "Test 2 failed";

  // Test 3: n=4
  p := CircleColoring(4, [1,1,1,1], [2,2,2,2], [3,3,3,3]);
  expect p == [3,2,3,2], "Test 3 failed";

  // Test 4: n=5
  p := CircleColoring(5, [1,2,3,4,5], [2,3,4,5,1], [3,4,5,1,2]);
  expect p == [3,4,5,1,2], "Test 4 failed";

  // Test 5: n=3
  p := CircleColoring(3, [10,20,30], [20,30,10], [30,10,20]);
  expect p == [30,10,20], "Test 5 failed";

  // Test 6, Case 1: n=3
  p := CircleColoring(3, [1,1,1], [2,2,2], [3,3,3]);
  expect p == [3,2,1], "Test 6.1 failed";

  // Test 6, Case 2: n=3
  p := CircleColoring(3, [5,6,7], [6,7,5], [7,5,6]);
  expect p == [7,5,6], "Test 6.2 failed";

  // Test 7: n=6
  p := CircleColoring(6, [1,1,2,2,3,3], [2,2,3,3,1,1], [3,3,1,1,2,2]);
  expect p == [3,2,1,3,2,1], "Test 7 failed";

  // Test 8: n=3
  p := CircleColoring(3, [1,1,2], [2,3,1], [3,2,3]);
  expect p == [3,2,1], "Test 8 failed";

  // Test 9: n=7
  p := CircleColoring(7, [1,2,1,2,1,2,1], [2,1,2,1,2,1,2], [3,3,3,3,3,3,3]);
  expect p == [3,1,3,1,3,1,2], "Test 9 failed";

  // Test 10, Case 1: n=3
  p := CircleColoring(3, [1,2,3], [3,1,2], [2,3,1]);
  expect p == [2,3,1], "Test 10.1 failed";

  // Test 10, Case 2: n=4
  p := CircleColoring(4, [5,5,5,5], [6,6,6,6], [7,7,7,7]);
  expect p == [7,6,7,6], "Test 10.2 failed";

  // Test 10, Case 3: n=5
  p := CircleColoring(5, [1,3,5,7,9], [2,4,6,8,10], [3,5,7,9,11]);
  expect p == [3,5,7,9,11], "Test 10.3 failed";

  // Test 11: n=10
  p := CircleColoring(10, [1,2,3,4,5,6,7,8,9,10], [2,3,4,5,6,7,8,9,10,1], [3,4,5,6,7,8,9,10,1,2]);
  expect p == [3,4,5,6,7,8,9,10,1,2], "Test 11 failed";

  print "All tests passed\n";
}
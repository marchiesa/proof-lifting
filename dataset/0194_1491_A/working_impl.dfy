method KthLargestValue(a: seq<int>, queries: seq<(int, int)>) returns (results: seq<int>)
{
  var arr := a;
  var s := 0;
  var i := 0;
  while i < |arr| {
    s := s + arr[i];
    i := i + 1;
  }

  results := [];
  i := 0;
  while i < |queries| {
    var t := queries[i].0;
    var x := queries[i].1;
    if t == 1 {
      s := s - arr[x - 1];
      arr := arr[x - 1 := 1 - arr[x - 1]];
      s := s + arr[x - 1];
    } else {
      if x <= s {
        results := results + [1];
      } else {
        results := results + [0];
      }
    }
    i := i + 1;
  }
}

method Main()
{
  // Test 1
  var r1 := KthLargestValue([1, 1, 0, 1, 0], [(2,3), (1,2), (2,3), (2,1), (2,5)]);
  expect r1 == [1, 0, 1, 0], "Test 1 failed";

  // Test 2
  var r2 := KthLargestValue([0], [(2,1)]);
  expect r2 == [0], "Test 2 failed";

  // Test 3
  var r3 := KthLargestValue([0, 1, 0], [(2,1), (1,2), (2,2), (2,3)]);
  expect r3 == [1, 0, 0], "Test 3 failed";

  // Test 4
  var r4 := KthLargestValue([1, 1, 1, 1], [(2,1), (2,4), (1,3)]);
  expect r4 == [1, 1], "Test 4 failed";

  // Test 5
  var r5 := KthLargestValue([0, 0], [(2,1), (1,1), (2,1), (1,1), (2,2)]);
  expect r5 == [0, 1, 0], "Test 5 failed";

  // Test 6
  var r6 := KthLargestValue([1, 0, 1, 0, 1], [(2,2), (1,4), (2,2), (1,5), (2,3), (2,5)]);
  expect r6 == [1, 1, 1, 0], "Test 6 failed";

  // Test 7
  var r7 := KthLargestValue([0], [(1,1), (2,1), (1,1)]);
  expect r7 == [1], "Test 7 failed";

  // Test 8
  var r8 := KthLargestValue([0, 0, 0, 0, 0, 0], [(2,6), (1,3), (2,1), (2,6)]);
  expect r8 == [0, 1, 0], "Test 8 failed";

  // Test 9
  var r9 := KthLargestValue([1, 0, 1, 1, 0, 0, 1], [(2,4), (1,7), (1,2), (2,1), (2,7)]);
  expect r9 == [1, 1, 0], "Test 9 failed";

  // Test 10
  var r10 := KthLargestValue([1, 1, 1], [(2,1), (1,1), (2,1), (1,2), (2,2), (2,3)]);
  expect r10 == [1, 1, 0, 0], "Test 10 failed";

  // Test 11
  var r11 := KthLargestValue([0, 1, 0, 1, 0, 1, 0, 1], [(2,4), (1,3), (2,4), (1,6), (2,5), (1,1), (2,8)]);
  expect r11 == [1, 1, 0, 0], "Test 11 failed";

  // Test 12
  var r12 := KthLargestValue([1, 0, 0, 1, 1, 0, 1, 0, 0, 1], [(2,5), (1,10), (2,1), (1,4), (2,6), (1,7), (2,10), (2,3)]);
  expect r12 == [1, 1, 0, 0, 0], "Test 12 failed";

  print "All tests passed\n";
}
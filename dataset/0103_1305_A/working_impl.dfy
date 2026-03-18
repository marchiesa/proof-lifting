method Insert(sorted: seq<int>, val: int) returns (result: seq<int>)
{
  var i := 0;
  while i < |sorted| && sorted[i] < val
  {
    i := i + 1;
  }
  result := sorted[..i] + [val] + sorted[i..];
}

method SortSeq(s: seq<int>) returns (sorted: seq<int>)
{
  sorted := [];
  var i := 0;
  while i < |s|
  {
    sorted := Insert(sorted, s[i]);
    i := i + 1;
  }
}

method KuroniAndTheGifts(a: seq<int>, b: seq<int>) returns (x: seq<int>, y: seq<int>)
{
  x := SortSeq(a);
  y := SortSeq(b);
}

method Main()
{
  // Test 1, Case 1
  var x1, y1 := KuroniAndTheGifts([1, 8, 5], [8, 4, 5]);
  expect x1 == [1, 5, 8], "Test 1.1 x failed";
  expect y1 == [4, 5, 8], "Test 1.1 y failed";

  // Test 1, Case 2
  var x2, y2 := KuroniAndTheGifts([1, 7, 5], [6, 1, 2]);
  expect x2 == [1, 5, 7], "Test 1.2 x failed";
  expect y2 == [1, 2, 6], "Test 1.2 y failed";

  // Test 2
  var x3, y3 := KuroniAndTheGifts([5], [3]);
  expect x3 == [5], "Test 2 x failed";
  expect y3 == [3], "Test 2 y failed";

  // Test 3
  var x4, y4 := KuroniAndTheGifts([1, 2], [3, 4]);
  expect x4 == [1, 2], "Test 3 x failed";
  expect y4 == [3, 4], "Test 3 y failed";

  // Test 4
  var x5, y5 := KuroniAndTheGifts([1, 7, 5], [6, 1, 2]);
  expect x5 == [1, 5, 7], "Test 4 x failed";
  expect y5 == [1, 2, 6], "Test 4 y failed";

  // Test 5
  var x6, y6 := KuroniAndTheGifts([1, 2, 3, 4, 5], [10, 20, 30, 40, 50]);
  expect x6 == [1, 2, 3, 4, 5], "Test 5 x failed";
  expect y6 == [10, 20, 30, 40, 50], "Test 5 y failed";

  // Test 6, Case 1
  var x7, y7 := KuroniAndTheGifts([1], [1]);
  expect x7 == [1], "Test 6.1 x failed";
  expect y7 == [1], "Test 6.1 y failed";

  // Test 6, Case 2
  var x8, y8 := KuroniAndTheGifts([3, 7], [5, 2]);
  expect x8 == [3, 7], "Test 6.2 x failed";
  expect y8 == [2, 5], "Test 6.2 y failed";

  // Test 7
  var x9, y9 := KuroniAndTheGifts([10, 20, 30, 40], [1, 2, 3, 4]);
  expect x9 == [10, 20, 30, 40], "Test 7 x failed";
  expect y9 == [1, 2, 3, 4], "Test 7 y failed";

  // Test 8, Case 1
  var x10, y10 := KuroniAndTheGifts([42], [17]);
  expect x10 == [42], "Test 8.1 x failed";
  expect y10 == [17], "Test 8.1 y failed";

  // Test 8, Case 2
  var x11, y11 := KuroniAndTheGifts([1, 3], [2, 4]);
  expect x11 == [1, 3], "Test 8.2 x failed";
  expect y11 == [2, 4], "Test 8.2 y failed";

  // Test 8, Case 3
  var x12, y12 := KuroniAndTheGifts([5, 10, 15], [1, 2, 3]);
  expect x12 == [5, 10, 15], "Test 8.3 x failed";
  expect y12 == [1, 2, 3], "Test 8.3 y failed";

  // Test 9
  var x13, y13 := KuroniAndTheGifts([1, 2, 3, 4, 5, 6, 7, 8, 9, 10], [11, 12, 13, 14, 15, 16, 17, 18, 19, 20]);
  expect x13 == [1, 2, 3, 4, 5, 6, 7, 8, 9, 10], "Test 9 x failed";
  expect y13 == [11, 12, 13, 14, 15, 16, 17, 18, 19, 20], "Test 9 y failed";

  // Test 10
  var x14, y14 := KuroniAndTheGifts([3, 1, 4, 1, 5, 9], [2, 7, 1, 8, 2, 8]);
  expect x14 == [1, 1, 3, 4, 5, 9], "Test 10 x failed";
  expect y14 == [1, 2, 2, 7, 8, 8], "Test 10 y failed";

  // Test 11, Case 1
  var x15, y15 := KuroniAndTheGifts([50, 40, 30, 20, 10], [5, 15, 25, 35, 45]);
  expect x15 == [10, 20, 30, 40, 50], "Test 11.1 x failed";
  expect y15 == [5, 15, 25, 35, 45], "Test 11.1 y failed";

  // Test 11, Case 2
  var x16, y16 := KuroniAndTheGifts([7, 3, 9, 1], [2, 8, 4, 6]);
  expect x16 == [1, 3, 7, 9], "Test 11.2 x failed";
  expect y16 == [2, 4, 6, 8], "Test 11.2 y failed";

  print "All tests passed\n";
}
method CancelTheTrains(bottom: seq<int>, left: seq<int>) returns (cancelled: int)
{
  cancelled := 0;
  var h: map<int, int> := map[];

  var i := 0;
  while i < |bottom|
  {
    var x := bottom[i];
    if x in h {
      h := h[x := h[x] + 1];
    } else {
      h := h[x := 1];
    }
    i := i + 1;
  }

  var j := 0;
  while j < |left|
  {
    var x := left[j];
    if x in h && h[x] == 1 {
      cancelled := cancelled + 1;
    }
    j := j + 1;
  }
}

method Main()
{
  var cancelled: int;

  // Test 1, Case 1: bottom=[1], left=[3,4] → 0
  cancelled := CancelTheTrains([1], [3, 4]);
  expect cancelled == 0, "Test 1.1 failed";

  // Test 1, Case 2: bottom=[1,3,4], left=[2,4] → 1
  cancelled := CancelTheTrains([1, 3, 4], [2, 4]);
  expect cancelled == 1, "Test 1.2 failed";

  // Test 1, Case 3: → 3
  cancelled := CancelTheTrains([2, 7, 16, 28, 33, 57, 59, 86, 99], [3, 9, 14, 19, 25, 26, 28, 35, 41, 59, 85, 87, 99, 100]);
  expect cancelled == 3, "Test 1.3 failed";

  // Test 2: bottom=[1], left=[1] → 1
  cancelled := CancelTheTrains([1], [1]);
  expect cancelled == 1, "Test 2 failed";

  // Test 3: bottom=[1,4], left=[2,3,5] → 0
  cancelled := CancelTheTrains([1, 4], [2, 3, 5]);
  expect cancelled == 0, "Test 3 failed";

  // Test 4: bottom=[1,2,3], left=[1,2,3] → 3
  cancelled := CancelTheTrains([1, 2, 3], [1, 2, 3]);
  expect cancelled == 3, "Test 4 failed";

  // Test 5: bottom=[1,2,3,4,5], left=[1,2,3,4,5] → 5
  cancelled := CancelTheTrains([1, 2, 3, 4, 5], [1, 2, 3, 4, 5]);
  expect cancelled == 5, "Test 5 failed";

  // Test 6: bottom=[3], left=[1,2,3,4,5] → 1
  cancelled := CancelTheTrains([3], [1, 2, 3, 4, 5]);
  expect cancelled == 1, "Test 6 failed";

  // Test 7: bottom=[2,5,7,8], left=[6] → 0
  cancelled := CancelTheTrains([2, 5, 7, 8], [6]);
  expect cancelled == 0, "Test 7 failed";

  // Test 8, Case 1: bottom=[3,7], left=[3,7] → 2
  cancelled := CancelTheTrains([3, 7], [3, 7]);
  expect cancelled == 2, "Test 8.1 failed";

  // Test 8, Case 2: bottom=[5], left=[5] → 1
  cancelled := CancelTheTrains([5], [5]);
  expect cancelled == 1, "Test 8.2 failed";

  // Test 9: bottom=[10,20,30], left=[5,10,20,40] → 2
  cancelled := CancelTheTrains([10, 20, 30], [5, 10, 20, 40]);
  expect cancelled == 2, "Test 9 failed";

  // Test 10, Case 1: bottom=[1], left=[1] → 1
  cancelled := CancelTheTrains([1], [1]);
  expect cancelled == 1, "Test 10.1 failed";

  // Test 10, Case 2: bottom=[1,2], left=[1,2] → 2
  cancelled := CancelTheTrains([1, 2], [1, 2]);
  expect cancelled == 2, "Test 10.2 failed";

  // Test 10, Case 3: bottom=[1,2,3], left=[4,5,6] → 0
  cancelled := CancelTheTrains([1, 2, 3], [4, 5, 6]);
  expect cancelled == 0, "Test 10.3 failed";

  // Test 11: bottom=[2,4,8,15,23,50], left=[1,4,9,15,30,42,50] → 3
  cancelled := CancelTheTrains([2, 4, 8, 15, 23, 50], [1, 4, 9, 15, 30, 42, 50]);
  expect cancelled == 3, "Test 11 failed";

  print "All tests passed\n";
}
method SortSeq(s: seq<int>) returns (sorted: seq<int>)
{
  var arr := s;
  for i := 1 to |arr| {
    var j := i;
    while j > 0 && arr[j - 1] > arr[j]
      decreases j
    {
      var tmp := arr[j];
      arr := arr[j := arr[j - 1]];
      arr := arr[j - 1 := tmp];
      j := j - 1;
    }
  }
  sorted := arr;
}

method Meximization(a: seq<int>) returns (b: seq<int>)
{
  var s: set<int> := {};
  var res: seq<int> := [];
  var ss: seq<int> := [];
  for i := 0 to |a| {
    var x := a[i];
    if x in s {
      ss := ss + [x];
    } else {
      res := res + [x];
    }
    s := s + {x};
  }
  res := SortSeq(res);
  b := res + ss;
}

method Main()
{
  // Test 1, case 1
  var r := Meximization([4, 2, 0, 1, 3, 3, 7]);
  expect r == [0, 1, 2, 3, 4, 7, 3], "Test 1.1 failed";

  // Test 1, case 2
  r := Meximization([2, 2, 8, 6, 9]);
  expect r == [2, 6, 8, 9, 2], "Test 1.2 failed";

  // Test 1, case 3
  r := Meximization([0]);
  expect r == [0], "Test 1.3 failed";

  // Test 2
  r := Meximization([2]);
  expect r == [2], "Test 2 failed";

  // Test 3
  var ones := seq(100, (i: int) => 1);
  r := Meximization(ones);
  expect r == ones, "Test 3 failed";

  // Test 4
  r := Meximization([0, 1, 2, 3, 4]);
  expect r == [0, 1, 2, 3, 4], "Test 4 failed";

  // Test 5
  r := Meximization([0, 0, 0, 0, 0, 0]);
  expect r == [0, 0, 0, 0, 0, 0], "Test 5 failed";

  // Test 6
  r := Meximization([0]);
  expect r == [0], "Test 6 failed";

  // Test 7
  r := Meximization([0, 1, 2, 3, 4, 5, 6, 7, 8, 9]);
  expect r == [0, 1, 2, 3, 4, 5, 6, 7, 8, 9], "Test 7 failed";

  // Test 8, case 1
  r := Meximization([3, 3, 3, 3]);
  expect r == [3, 3, 3, 3], "Test 8.1 failed";

  // Test 8, case 2
  r := Meximization([0, 1, 0]);
  expect r == [0, 1, 0], "Test 8.2 failed";

  // Test 9
  r := Meximization([0, 1, 0, 1, 0, 1, 2, 3]);
  expect r == [0, 1, 2, 3, 0, 1, 0, 1], "Test 9 failed";

  // Test 10
  r := Meximization([5, 6, 7, 8, 9]);
  expect r == [5, 6, 7, 8, 9], "Test 10 failed";

  // Test 11, case 1
  r := Meximization([0, 0]);
  expect r == [0, 0], "Test 11.1 failed";

  // Test 11, case 2
  r := Meximization([0, 1, 2]);
  expect r == [0, 1, 2], "Test 11.2 failed";

  // Test 11, case 3
  r := Meximization([1, 2, 3, 4]);
  expect r == [1, 2, 3, 4], "Test 11.3 failed";

  // Test 12
  r := Meximization([0, 1, 2, 0, 1, 2, 0, 1, 2, 3]);
  expect r == [0, 1, 2, 3, 0, 1, 2, 0, 1, 2], "Test 12 failed";

  print "All tests passed\n";
}
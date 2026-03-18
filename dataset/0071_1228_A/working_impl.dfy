method DistinctDigits(l: int, r: int) returns (x: int)
{
  var i := l;
  while i <= r
  {
    var cnt := new int[10](_ => 0);
    var n := i;
    var ok := true;
    while n > 0
    {
      var d := n % 10;
      cnt[d] := cnt[d] + 1;
      if cnt[d] > 1 {
        ok := false;
      }
      n := n / 10;
    }
    if ok {
      return i;
    }
    i := i + 1;
  }
  return -1;
}

method Main()
{
  var result: int;

  result := DistinctDigits(121, 130);
  expect result == 123, "Test 1 failed";

  result := DistinctDigits(98766, 100000);
  expect result == -1, "Test 2 failed";

  result := DistinctDigits(25610, 80988);
  expect result == 25610, "Test 3 failed";

  result := DistinctDigits(76330, 80769);
  expect result == 76340, "Test 4 failed";

  result := DistinctDigits(23452, 23456);
  expect result == 23456, "Test 5 failed";

  result := DistinctDigits(47142, 47149);
  expect result == -1, "Test 6 failed";

  result := DistinctDigits(1, 1);
  expect result == 1, "Test 7 failed";

  result := DistinctDigits(10, 10);
  expect result == 10, "Test 8 failed";

  result := DistinctDigits(25139, 86116);
  expect result == 25139, "Test 9 failed";

  result := DistinctDigits(9878, 9999);
  expect result == -1, "Test 10 failed";

  result := DistinctDigits(5, 5);
  expect result == 5, "Test 11 failed";

  result := DistinctDigits(8563, 90197);
  expect result == 8563, "Test 12 failed";

  result := DistinctDigits(1, 100000);
  expect result == 1, "Test 13 failed";

  result := DistinctDigits(112, 112);
  expect result == -1, "Test 14 failed";

  result := DistinctDigits(99, 101);
  expect result == -1, "Test 15 failed";

  result := DistinctDigits(99, 1000);
  expect result == 102, "Test 16 failed";

  result := DistinctDigits(999, 1002);
  expect result == -1, "Test 17 failed";

  result := DistinctDigits(111, 121);
  expect result == 120, "Test 18 failed";

  result := DistinctDigits(22, 22);
  expect result == -1, "Test 19 failed";

  print "All tests passed\n";
}
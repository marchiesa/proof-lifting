method TanyaAndStairways(a: seq<int>) returns (t: int, stairs: seq<int>)
{
  stairs := [];
  var cnt := 0;
  for i := 0 to |a| {
    if i == 0 {
      cnt := 1;
    } else if a[i] == 1 {
      stairs := stairs + [cnt];
      cnt := 1;
    } else {
      cnt := cnt + 1;
    }
  }
  stairs := stairs + [cnt];
  t := |stairs|;
}

method Main()
{
  // Test 1
  var t1, s1 := TanyaAndStairways([1, 2, 3, 1, 2, 3, 4]);
  expect t1 == 2, "Test 1: t mismatch";
  expect s1 == [3, 4], "Test 1: stairs mismatch";

  // Test 2
  var t2, s2 := TanyaAndStairways([1, 1, 1, 1]);
  expect t2 == 4, "Test 2: t mismatch";
  expect s2 == [1, 1, 1, 1], "Test 2: stairs mismatch";

  // Test 3
  var t3, s3 := TanyaAndStairways([1, 2, 3, 4, 5]);
  expect t3 == 1, "Test 3: t mismatch";
  expect s3 == [5], "Test 3: stairs mismatch";

  // Test 4
  var t4, s4 := TanyaAndStairways([1, 2, 1, 2, 1]);
  expect t4 == 3, "Test 4: t mismatch";
  expect s4 == [2, 2, 1], "Test 4: stairs mismatch";

  // Test 5
  var t5, s5 := TanyaAndStairways([1]);
  expect t5 == 1, "Test 5: t mismatch";
  expect s5 == [1], "Test 5: stairs mismatch";

  // Test 6
  var t6, s6 := TanyaAndStairways([1, 2, 3, 4, 1, 2, 3, 1, 1, 2, 3, 1, 2, 3, 4, 1, 1, 2, 3, 4, 1, 2, 3, 4, 1, 2, 3, 4, 1, 1, 2, 1, 2, 1, 2, 1, 1, 2, 1, 2, 1, 2, 3, 1, 2, 1, 2, 1]);
  expect t6 == 20, "Test 6: t mismatch";
  expect s6 == [4, 3, 1, 3, 4, 1, 4, 4, 4, 1, 2, 2, 2, 1, 2, 2, 3, 2, 2, 1], "Test 6: stairs mismatch";

  // Test 7
  var t7, s7 := TanyaAndStairways([1, 2]);
  expect t7 == 1, "Test 7: t mismatch";
  expect s7 == [2], "Test 7: stairs mismatch";

  // Test 8
  var t8, s8 := TanyaAndStairways([1, 1, 2]);
  expect t8 == 2, "Test 8: t mismatch";
  expect s8 == [1, 2], "Test 8: stairs mismatch";

  // Test 9
  var t9, s9 := TanyaAndStairways([1, 1, 2, 3]);
  expect t9 == 2, "Test 9: t mismatch";
  expect s9 == [1, 3], "Test 9: stairs mismatch";

  // Test 10
  var t10, s10 := TanyaAndStairways([1, 2, 3, 1, 2, 3, 4, 5]);
  expect t10 == 2, "Test 10: t mismatch";
  expect s10 == [3, 5], "Test 10: stairs mismatch";

  // Test 11
  var t11, s11 := TanyaAndStairways([1, 1, 1, 2, 3]);
  expect t11 == 3, "Test 11: t mismatch";
  expect s11 == [1, 1, 3], "Test 11: stairs mismatch";

  print "All tests passed\n";
}
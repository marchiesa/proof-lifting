method NearlyLucky(n: int) returns (result: bool)
{
  var num := if n < 0 then -n else n;
  if num == 0 {
    result := false;
    return;
  }
  var count := 0;
  var temp := num;
  while temp > 0 {
    var digit := temp % 10;
    if digit == 4 || digit == 7 {
      count := count + 1;
    }
    temp := temp / 10;
  }
  if count == 0 {
    result := false;
    return;
  }
  var flag := true;
  temp := count;
  while temp > 0 {
    var digit := temp % 10;
    if digit != 4 && digit != 7 {
      flag := false;
    }
    temp := temp / 10;
  }
  result := flag;
}

method Main()
{
  var r1 := NearlyLucky(40047);
  expect r1 == false, "Test 1 failed";

  var r2 := NearlyLucky(7747774);
  expect r2 == true, "Test 2 failed";

  var r3 := NearlyLucky(1000000000000000000);
  expect r3 == false, "Test 3 failed";

  var r4 := NearlyLucky(7);
  expect r4 == false, "Test 4 failed";

  var r5 := NearlyLucky(4);
  expect r5 == false, "Test 5 failed";

  var r6 := NearlyLucky(474404774);
  expect r6 == false, "Test 6 failed";

  var r7 := NearlyLucky(4744000695826);
  expect r7 == true, "Test 7 failed";

  var r8 := NearlyLucky(10000000004744744);
  expect r8 == true, "Test 8 failed";

  var r9 := NearlyLucky(446486416781684178);
  expect r9 == true, "Test 9 failed";

  var r10 := NearlyLucky(999999999);
  expect r10 == false, "Test 10 failed";

  var r11 := NearlyLucky(7777);
  expect r11 == true, "Test 11 failed";

  var r12 := NearlyLucky(87414417444);
  expect r12 == false, "Test 12 failed";

  var r13 := NearlyLucky(111222333444555667);
  expect r13 == true, "Test 13 failed";

  var r14 := NearlyLucky(1);
  expect r14 == false, "Test 14 failed";

  var r15 := NearlyLucky(4700);
  expect r15 == false, "Test 15 failed";

  var r16 := NearlyLucky(3794555488744477);
  expect r16 == false, "Test 16 failed";

  var r17 := NearlyLucky(444444444444444444);
  expect r17 == false, "Test 17 failed";

  var r18 := NearlyLucky(474447447774444774);
  expect r18 == false, "Test 18 failed";

  var r19 := NearlyLucky(777777777777777);
  expect r19 == false, "Test 19 failed";

  var r20 := NearlyLucky(34777745021000000);
  expect r20 == false, "Test 20 failed";

  print "All tests passed\n";
}
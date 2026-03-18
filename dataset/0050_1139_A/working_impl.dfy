method EvenSubstrings(s: string) returns (count: int)
{
  count := 0;
  for i := 0 to |s| {
    if s[i] == '0' || s[i] == '2' || s[i] == '4' || s[i] == '6' || s[i] == '8' {
      count := count + i + 1;
    }
  }
}

method Main()
{
  var r1 := EvenSubstrings("1234");
  expect r1 == 6, "Test 1 failed";

  var r2 := EvenSubstrings("2244");
  expect r2 == 10, "Test 2 failed";

  var r3 := EvenSubstrings("3");
  expect r3 == 0, "Test 3 failed";

  var r4 := EvenSubstrings("6");
  expect r4 == 1, "Test 4 failed";

  var r5 := EvenSubstrings("9572683145");
  expect r5 == 24, "Test 5 failed";

  var r6 := EvenSubstrings("13");
  expect r6 == 0, "Test 6 failed";

  var r7 := EvenSubstrings("18");
  expect r7 == 2, "Test 7 failed";

  var r8 := EvenSubstrings("81");
  expect r8 == 1, "Test 8 failed";

  var r9 := EvenSubstrings("68");
  expect r9 == 3, "Test 9 failed";

  var r10 := EvenSubstrings("111");
  expect r10 == 0, "Test 10 failed";

  var r11 := EvenSubstrings("112");
  expect r11 == 3, "Test 11 failed";

  var r12 := EvenSubstrings("121");
  expect r12 == 2, "Test 12 failed";

  var r13 := EvenSubstrings("122");
  expect r13 == 5, "Test 13 failed";

  var r14 := EvenSubstrings("211");
  expect r14 == 1, "Test 14 failed";

  var r15 := EvenSubstrings("212");
  expect r15 == 4, "Test 15 failed";

  var r16 := EvenSubstrings("221");
  expect r16 == 3, "Test 16 failed";

  var r17 := EvenSubstrings("222");
  expect r17 == 6, "Test 17 failed";

  var r18 := EvenSubstrings("263254663359864483324578786753512345165");
  expect r18 == 327, "Test 18 failed";

  print "All tests passed\n";
}
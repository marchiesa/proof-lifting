method InGameChat(s: string) returns (bad: bool)
{
  var i := |s| - 1;
  while i >= 0 && s[i] == ')'
  {
    i := i - 1;
  }
  var x := |s| - i - 1;
  bad := x > |s| - x;
}

method Main()
{
  // Test 1
  var r1 := InGameChat("))");
  expect r1 == true, "Test 1.1 failed";

  var r2 := InGameChat("gl))hf))))))");
  expect r2 == false, "Test 1.2 failed";

  var r3 := InGameChat("gege)))))");
  expect r3 == true, "Test 1.3 failed";

  var r4 := InGameChat(")aa))b))))))))");
  expect r4 == true, "Test 1.4 failed";

  var r5 := InGameChat(")");
  expect r5 == true, "Test 1.5 failed";

  // Test 2
  var r6 := InGameChat("aaaaa)");
  expect r6 == false, "Test 2.1 failed";

  var r7 := InGameChat("))))))");
  expect r7 == true, "Test 2.2 failed";

  // Test 3
  var r8 := InGameChat("aaaa");
  expect r8 == false, "Test 3 failed";

  // Test 4
  var r9 := InGameChat("sa)ttttttt");
  expect r9 == false, "Test 4 failed";

  // Test 5
  var r10 := InGameChat("abcd)))");
  expect r10 == false, "Test 5 failed";

  // Test 6
  var r11 := InGameChat("k");
  expect r11 == false, "Test 6 failed";

  // Test 7
  var r12 := InGameChat("g");
  expect r12 == false, "Test 7 failed";

  // Test 8
  var r13 := InGameChat("a");
  expect r13 == false, "Test 8 failed";

  // Test 9
  var r14 := InGameChat("aaaaa");
  expect r14 == false, "Test 9 failed";

  print "All tests passed\n";
}
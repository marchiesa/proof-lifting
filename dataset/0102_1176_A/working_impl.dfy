method DivideIt(n: int) returns (ans: int)
{
  ans := 0;
  var m := n;
  while m % 2 == 0 {
    ans := ans + 1;
    m := m / 2;
  }
  while m % 3 == 0 {
    ans := ans + 2;
    m := m / 3;
  }
  while m % 5 == 0 {
    ans := ans + 3;
    m := m / 5;
  }
  if m != 1 {
    ans := -1;
  }
  return;
}

method Main()
{
  // Test 1 cases
  var r1 := DivideIt(1);
  expect r1 == 0, "DivideIt(1) failed";

  var r2 := DivideIt(10);
  expect r2 == 4, "DivideIt(10) failed";

  var r3 := DivideIt(25);
  expect r3 == 6, "DivideIt(25) failed";

  var r4 := DivideIt(30);
  expect r4 == 6, "DivideIt(30) failed";

  var r5 := DivideIt(14);
  expect r5 == -1, "DivideIt(14) failed";

  var r6 := DivideIt(27);
  expect r6 == 6, "DivideIt(27) failed";

  var r7 := DivideIt(1000000000000000000);
  expect r7 == 72, "DivideIt(1000000000000000000) failed";

  // Test 2
  var r8 := DivideIt(22876792454961);
  expect r8 == 56, "DivideIt(22876792454961) failed";

  // Test 3
  var r9 := DivideIt(70745089028899904);
  expect r9 == -1, "DivideIt(70745089028899904) failed";

  // Test 4
  var r10 := DivideIt(576460752303423487);
  expect r10 == -1, "DivideIt(576460752303423487) failed";

  // Test 5
  var r11 := DivideIt(1);
  expect r11 == 0, "DivideIt(1) [test5] failed";

  // Test 6
  var r12 := DivideIt(30);
  expect r12 == 6, "DivideIt(30) [test6] failed";

  print "All tests passed\n";
}
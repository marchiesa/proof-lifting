method TwoBrackets(s: string) returns (moves: int)
{
  var openCount := new int[2];
  openCount[0] := 0;
  openCount[1] := 0;
  moves := 0;
  var j := 0;
  while j < |s|
  {
    var c := s[j];
    var i := if c == '[' || c == ']' then 1 else 0;
    if c == '(' || c == '[' {
      openCount[i] := openCount[i] + 1;
    } else if openCount[i] > 0 {
      openCount[i] := openCount[i] - 1;
      moves := moves + 1;
    }
    j := j + 1;
  }
}

method Main()
{
  // Test 1
  var r1 := TwoBrackets("()");
  expect r1 == 1, "Test 1.1 failed";

  var r2 := TwoBrackets("[]()");
  expect r2 == 2, "Test 1.2 failed";

  var r3 := TwoBrackets("([)]");
  expect r3 == 2, "Test 1.3 failed";

  var r4 := TwoBrackets(")]([");
  expect r4 == 0, "Test 1.4 failed";

  var r5 := TwoBrackets(")[(]");
  expect r5 == 1, "Test 1.5 failed";

  // Test 2
  var r6 := TwoBrackets("[()]");
  expect r6 == 2, "Test 2.1 failed";

  var r7 := TwoBrackets("[]");
  expect r7 == 1, "Test 2.2 failed";

  var r8 := TwoBrackets("[]");
  expect r8 == 1, "Test 2.3 failed";

  var r9 := TwoBrackets("()");
  expect r9 == 1, "Test 2.4 failed";

  // Test 3
  var r10 := TwoBrackets("()");
  expect r10 == 1, "Test 3.1 failed";

  var r11 := TwoBrackets("()");
  expect r11 == 1, "Test 3.2 failed";

  var r12 := TwoBrackets("()");
  expect r12 == 1, "Test 3.3 failed";

  var r13 := TwoBrackets("()");
  expect r13 == 1, "Test 3.4 failed";

  // Test 4
  var r14 := TwoBrackets("()");
  expect r14 == 1, "Test 4.1 failed";

  var r15 := TwoBrackets("()");
  expect r15 == 1, "Test 4.2 failed";

  var r16 := TwoBrackets("()");
  expect r16 == 1, "Test 4.3 failed";

  var r17 := TwoBrackets("()");
  expect r17 == 1, "Test 4.4 failed";

  var r18 := TwoBrackets("()");
  expect r18 == 1, "Test 4.5 failed";

  var r19 := TwoBrackets("()");
  expect r19 == 1, "Test 4.6 failed";

  var r20 := TwoBrackets("()");
  expect r20 == 1, "Test 4.7 failed";

  print "All tests passed\n";
}
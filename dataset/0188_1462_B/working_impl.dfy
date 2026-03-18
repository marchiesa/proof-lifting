method LastYearSubstring(s: string) returns (result: bool)
{
  var n := |s|;
  if n < 4 {
    result := false;
    return;
  }
  var c1 := s[0..4] == "2020";
  var c2 := s[n-4..n] == "2020";
  var c3 := s[0] == '2' && s[n-3..n] == "020";
  var c4 := s[0..2] == "20" && s[n-2..n] == "20";
  var c5 := s[0..3] == "202" && s[n-1] == '0';
  result := c1 || c2 || c3 || c4 || c5;
}

method Main()
{
  // Test 1 cases
  var r1 := LastYearSubstring("20192020");
  expect r1 == true, "Test 1a failed: expected true for \"20192020\"";

  var r2 := LastYearSubstring("22019020");
  expect r2 == true, "Test 1b failed: expected true for \"22019020\"";

  var r3 := LastYearSubstring("2020");
  expect r3 == true, "Test 1c failed: expected true for \"2020\"";

  var r4 := LastYearSubstring("20002");
  expect r4 == false, "Test 1d failed: expected false for \"20002\"";

  var r5 := LastYearSubstring("729040");
  expect r5 == false, "Test 1e failed: expected false for \"729040\"";

  var r6 := LastYearSubstring("200200");
  expect r6 == false, "Test 1f failed: expected false for \"200200\"";

  // Test 2
  var r7 := LastYearSubstring("2021");
  expect r7 == false, "Test 2 failed: expected false for \"2021\"";

  // Test 3
  var r8 := LastYearSubstring("2029");
  expect r8 == false, "Test 3 failed: expected false for \"2029\"";

  // Test 4
  var r9 := LastYearSubstring("2030");
  expect r9 == false, "Test 4 failed: expected false for \"2030\"";

  // Test 5
  var r10 := LastYearSubstring("2040");
  expect r10 == false, "Test 5 failed: expected false for \"2040\"";

  // Test 6
  var r11 := LastYearSubstring("2050");
  expect r11 == false, "Test 6 failed: expected false for \"2050\"";

  // Test 7
  var r12 := LastYearSubstring("2090");
  expect r12 == false, "Test 7 failed: expected false for \"2090\"";

  // Test 8
  var r13 := LastYearSubstring("2080");
  expect r13 == false, "Test 8 failed: expected false for \"2080\"";

  // Test 9
  var r14 := LastYearSubstring("2070");
  expect r14 == false, "Test 9 failed: expected false for \"2070\"";

  // Test 10
  var r15 := LastYearSubstring("2060");
  expect r15 == false, "Test 10 failed: expected false for \"2060\"";

  // Test 11
  var r16 := LastYearSubstring("2033");
  expect r16 == false, "Test 11 failed: expected false for \"2033\"";

  // Test 12
  var r17 := LastYearSubstring("2043");
  expect r17 == false, "Test 12 failed: expected false for \"2043\"";

  // Test 13
  var r18 := LastYearSubstring("2069");
  expect r18 == false, "Test 13 failed: expected false for \"2069\"";

  // Test 14
  var r19 := LastYearSubstring("2089");
  expect r19 == false, "Test 14 failed: expected false for \"2089\"";

  // Test 15
  var r20 := LastYearSubstring("2055");
  expect r20 == false, "Test 15 failed: expected false for \"2055\"";

  // Test 16
  var r21 := LastYearSubstring("2065");
  expect r21 == false, "Test 16 failed: expected false for \"2065\"";

  // Test 17
  var r22 := LastYearSubstring("2092");
  expect r22 == false, "Test 17 failed: expected false for \"2092\"";

  // Test 18
  var r23 := LastYearSubstring("2099");
  expect r23 == false, "Test 18 failed: expected false for \"2099\"";

  // Test 19
  var r24 := LastYearSubstring("2088");
  expect r24 == false, "Test 19 failed: expected false for \"2088\"";

  // Test 20
  var r25 := LastYearSubstring("2077");
  expect r25 == false, "Test 20 failed: expected false for \"2077\"";

  print "All tests passed\n";
}
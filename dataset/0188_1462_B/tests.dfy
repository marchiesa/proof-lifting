const TARGET: string := "2020"

predicate CanObtain2020(s: string)
{
  exists i | 0 <= i <= |s| ::
    exists j | i <= j <= |s| ::
      s[..i] + s[j..] == TARGET
}

method LastYearSubstring(s: string) returns (result: bool)
  ensures result == CanObtain2020(s)
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
  // ===== SPEC POSITIVE TESTS =====
  // Test CanObtain2020 with correct expected outputs, small inputs only

  // Test 1 true cases (scaled down from length-8 originals)
  expect CanObtain2020("2020") == true, "spec positive 1";    // from "2020"
  expect CanObtain2020("x2020") == true, "spec positive 2";   // scaled from "20192020" (suffix match)
  expect CanObtain2020("2x020") == true, "spec positive 3";   // scaled from "22019020" (split 1+3)

  // Test 1 false cases (already small)
  expect CanObtain2020("20002") == false, "spec positive 4";
  expect CanObtain2020("200200") == false, "spec positive 5";

  // Tests 2-10 (all length 4, already small)
  expect CanObtain2020("2021") == false, "spec positive 6";
  expect CanObtain2020("2029") == false, "spec positive 7";
  expect CanObtain2020("2030") == false, "spec positive 8";
  expect CanObtain2020("2040") == false, "spec positive 9";
  expect CanObtain2020("2050") == false, "spec positive 10";
  expect CanObtain2020("2090") == false, "spec positive 11";
  expect CanObtain2020("2080") == false, "spec positive 12";
  expect CanObtain2020("2070") == false, "spec positive 13";
  expect CanObtain2020("2060") == false, "spec positive 14";

  // ===== SPEC NEGATIVE TESTS =====
  // Wrong outputs should be rejected: negatives 2-10 claim true, but correct is false
  // Test: CanObtain2020(input) != wrong_output

  expect CanObtain2020("2021") != true, "spec negative 1";   // Negative 2
  expect CanObtain2020("2029") != true, "spec negative 2";   // Negative 3
  expect CanObtain2020("2030") != true, "spec negative 3";   // Negative 4
  expect CanObtain2020("2040") != true, "spec negative 4";   // Negative 5
  expect CanObtain2020("2050") != true, "spec negative 5";   // Negative 6
  expect CanObtain2020("2090") != true, "spec negative 6";   // Negative 7
  expect CanObtain2020("2080") != true, "spec negative 7";   // Negative 8
  expect CanObtain2020("2070") != true, "spec negative 8";   // Negative 9
  expect CanObtain2020("2060") != true, "spec negative 9";   // Negative 10

  // ===== IMPLEMENTATION TESTS =====
  // Full-size test pairs using the method

  // Test 1
  var r1 := LastYearSubstring("20192020");
  expect r1 == true, "impl test 1a failed";

  var r2 := LastYearSubstring("22019020");
  expect r2 == true, "impl test 1b failed";

  var r3 := LastYearSubstring("2020");
  expect r3 == true, "impl test 1c failed";

  var r4 := LastYearSubstring("20002");
  expect r4 == false, "impl test 1d failed";

  var r5 := LastYearSubstring("729040");
  expect r5 == false, "impl test 1e failed";

  var r6 := LastYearSubstring("200200");
  expect r6 == false, "impl test 1f failed";

  // Test 2
  var r7 := LastYearSubstring("2021");
  expect r7 == false, "impl test 2 failed";

  // Test 3
  var r8 := LastYearSubstring("2029");
  expect r8 == false, "impl test 3 failed";

  // Test 4
  var r9 := LastYearSubstring("2030");
  expect r9 == false, "impl test 4 failed";

  // Test 5
  var r10 := LastYearSubstring("2040");
  expect r10 == false, "impl test 5 failed";

  // Test 6
  var r11 := LastYearSubstring("2050");
  expect r11 == false, "impl test 6 failed";

  // Test 7
  var r12 := LastYearSubstring("2090");
  expect r12 == false, "impl test 7 failed";

  // Test 8
  var r13 := LastYearSubstring("2080");
  expect r13 == false, "impl test 8 failed";

  // Test 9
  var r14 := LastYearSubstring("2070");
  expect r14 == false, "impl test 9 failed";

  // Test 10
  var r15 := LastYearSubstring("2060");
  expect r15 == false, "impl test 10 failed";

  // Test 11
  var r16 := LastYearSubstring("2033");
  expect r16 == false, "impl test 11 failed";

  // Test 12
  var r17 := LastYearSubstring("2043");
  expect r17 == false, "impl test 12 failed";

  // Test 13
  var r18 := LastYearSubstring("2069");
  expect r18 == false, "impl test 13 failed";

  // Test 14
  var r19 := LastYearSubstring("2089");
  expect r19 == false, "impl test 14 failed";

  // Test 15
  var r20 := LastYearSubstring("2055");
  expect r20 == false, "impl test 15 failed";

  // Test 16
  var r21 := LastYearSubstring("2065");
  expect r21 == false, "impl test 16 failed";

  // Test 17
  var r22 := LastYearSubstring("2092");
  expect r22 == false, "impl test 17 failed";

  // Test 18
  var r23 := LastYearSubstring("2099");
  expect r23 == false, "impl test 18 failed";

  // Test 19
  var r24 := LastYearSubstring("2088");
  expect r24 == false, "impl test 19 failed";

  // Test 20
  var r25 := LastYearSubstring("2077");
  expect r25 == false, "impl test 20 failed";

  print "All tests passed\n";
}
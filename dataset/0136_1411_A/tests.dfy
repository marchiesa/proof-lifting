function TrailingParens(s: string): nat
  decreases |s|
{
  if |s| == 0 then 0
  else if s[|s| - 1] == ')' then 1 + TrailingParens(s[..|s| - 1])
  else 0
}

predicate IsBad(s: string)
{
  TrailingParens(s) > |s| - TrailingParens(s)
}

method InGameChat(s: string) returns (bad: bool)
  ensures bad == IsBad(s)
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
  // === SPEC POSITIVE TESTS ===
  // IsBad(input) == correct_output, small inputs only

  // From ")" -> Yes (length 1)
  expect IsBad(")") == true, "spec positive 1";
  // From "))" -> Yes (length 2)
  expect IsBad("))") == true, "spec positive 2";
  // From "k" -> No (length 1)
  expect IsBad("k") == false, "spec positive 3";
  // From "g" -> No (length 1)
  expect IsBad("g") == false, "spec positive 4";
  // From "a" -> No (length 1)
  expect IsBad("a") == false, "spec positive 5";
  // Scaled from "aaaa" -> No: "aa" (length 2, no trailing parens)
  expect IsBad("aa") == false, "spec positive 6";
  // Scaled from "))))))" -> Yes: ")))" (length 3, all parens)
  expect IsBad(")))") == true, "spec positive 7";
  // Scaled from "aaaaa)" -> No: "a)" (length 2, 1 trailing vs 1 non-trailing)
  expect IsBad("a)") == false, "spec positive 8";
  // Scaled from "gege)))))" -> Yes: "a))" (length 3, 2 trailing > 1 non-trailing)
  expect IsBad("a))") == true, "spec positive 9";

  // === SPEC NEGATIVE TESTS ===
  // IsBad(input) != wrong_output, small inputs only

  // Neg 1: ")" correct=true, wrong=false
  expect IsBad(")") != false, "spec negative 1";
  // Neg 2: scaled "))))))" -> ")))", correct=true, wrong=false
  expect IsBad(")))") != false, "spec negative 2";
  // Neg 3: scaled "aaaa" -> "aa", correct=false, wrong=true
  expect IsBad("aa") != true, "spec negative 3";
  // Neg 5: scaled "abcd)))" -> "a)", correct=false, wrong=true
  expect IsBad("a)") != true, "spec negative 4";
  // Neg 6: "k", correct=false, wrong=true
  expect IsBad("k") != true, "spec negative 5";
  // Neg 7: "g", correct=false, wrong=true
  expect IsBad("g") != true, "spec negative 6";
  // Neg 8: "a", correct=false, wrong=true
  expect IsBad("a") != true, "spec negative 7";
  // Neg 9: scaled "aaaaa" -> "aaa", correct=false, wrong=true
  expect IsBad("aaa") != true, "spec negative 8";
  // Neg 4: scaled "sa)ttttttt" -> "ab" (no trailing parens), correct=false, wrong=true
  expect IsBad("ab") != true, "spec negative 9";

  // === IMPLEMENTATION TESTS ===
  // Test 1
  var r1 := InGameChat("))");
  expect r1 == true, "impl test 1.1 failed";

  var r2 := InGameChat("gl))hf))))))");
  expect r2 == false, "impl test 1.2 failed";

  var r3 := InGameChat("gege)))))");
  expect r3 == true, "impl test 1.3 failed";

  var r4 := InGameChat(")aa))b))))))))");
  expect r4 == true, "impl test 1.4 failed";

  var r5 := InGameChat(")");
  expect r5 == true, "impl test 1.5 failed";

  // Test 2
  var r6 := InGameChat("aaaaa)");
  expect r6 == false, "impl test 2.1 failed";

  var r7 := InGameChat("))))))");
  expect r7 == true, "impl test 2.2 failed";

  // Test 3
  var r8 := InGameChat("aaaa");
  expect r8 == false, "impl test 3 failed";

  // Test 4
  var r9 := InGameChat("sa)ttttttt");
  expect r9 == false, "impl test 4 failed";

  // Test 5
  var r10 := InGameChat("abcd)))");
  expect r10 == false, "impl test 5 failed";

  // Test 6
  var r11 := InGameChat("k");
  expect r11 == false, "impl test 6 failed";

  // Test 7
  var r12 := InGameChat("g");
  expect r12 == false, "impl test 7 failed";

  // Test 8
  var r13 := InGameChat("a");
  expect r13 == false, "impl test 8 failed";

  // Test 9
  var r14 := InGameChat("aaaaa");
  expect r14 == false, "impl test 9 failed";

  print "All tests passed\n";
}
predicate IsBinaryChar(c: char)
{
  c == '0' || c == '1'
}

predicate IsBinaryString(s: string)
{
  forall i | 0 <= i < |s| :: IsBinaryChar(s[i])
}

predicate Similar(a: string, b: string)
{
  |a| == |b| && exists i | 0 <= i < |a| :: a[i] == b[i]
}

predicate StringSimilaritySpec(n: int, s: string, w: string)
  requires n >= 1
  requires |s| == 2 * n - 1
  requires IsBinaryString(s)
{
  |w| == n && IsBinaryString(w) && forall j | 0 <= j < n :: Similar(w, s[j..j + n])
}

method StringSimilarity(n: int, s: string) returns (w: string)
  requires n >= 1
  requires |s| == 2 * n - 1
  requires IsBinaryString(s)
  ensures |w| == n
  ensures IsBinaryString(w)
  ensures forall j | 0 <= j < n :: Similar(w, s[j..j + n])
{
  var c := s[n - 1];
  w := "";
  var i := 0;
  while i < n
  {
    w := w + [c];
    i := i + 1;
  }
}

method Main()
{
  // === SPEC POSITIVE TESTS (small inputs, n <= 3) ===
  expect StringSimilaritySpec(1, "1", "1"), "spec positive 1";
  expect StringSimilaritySpec(1, "0", "0"), "spec positive 2";
  expect StringSimilaritySpec(2, "101", "00"), "spec positive 3";
  expect StringSimilaritySpec(2, "110", "11"), "spec positive 4";
  expect StringSimilaritySpec(2, "010", "11"), "spec positive 5";
  expect StringSimilaritySpec(3, "00000", "000"), "spec positive 6";
  expect StringSimilaritySpec(3, "01010", "000"), "spec positive 7";
  expect StringSimilaritySpec(3, "10101", "111"), "spec positive 8";
  expect StringSimilaritySpec(3, "11100", "111"), "spec positive 9";

  // === SPEC NEGATIVE TESTS (small inputs, n <= 3) ===
  expect !StringSimilaritySpec(1, "1", "2"), "spec negative 1";
  expect !StringSimilaritySpec(1, "0", "1"), "spec negative 2";
  expect !StringSimilaritySpec(2, "110", "12"), "spec negative 3";
  expect !StringSimilaritySpec(3, "01010", "1"), "spec negative 4";
  expect !StringSimilaritySpec(3, "10101", "112"), "spec negative 5";

  // === IMPLEMENTATION TESTS (full-size inputs) ===
  var r1 := StringSimilarity(1, "1");
  expect r1 == "1", "impl test 1 failed";

  var r2 := StringSimilarity(3, "00000");
  expect r2 == "000", "impl test 2 failed";

  var r3 := StringSimilarity(4, "1110000");
  expect r3 == "0000", "impl test 3 failed";

  var r4 := StringSimilarity(2, "101");
  expect r4 == "00", "impl test 4 failed";

  var r5 := StringSimilarity(7, "0000000000001");
  expect r5 == "0000000", "impl test 5 failed";

  var r6 := StringSimilarity(1, "0");
  expect r6 == "0", "impl test 6 failed";

  var r7 := StringSimilarity(2, "110");
  expect r7 == "11", "impl test 7 failed";

  var r8 := StringSimilarity(5, "000000000");
  expect r8 == "00000", "impl test 8 failed";

  var r9 := StringSimilarity(5, "111111111");
  expect r9 == "11111", "impl test 9 failed";

  var r10 := StringSimilarity(3, "01010");
  expect r10 == "000", "impl test 10 failed";

  var r11 := StringSimilarity(4, "1001110");
  expect r11 == "1111", "impl test 11 failed";

  var r12 := StringSimilarity(3, "10101");
  expect r12 == "111", "impl test 12 failed";

  var r13 := StringSimilarity(2, "010");
  expect r13 == "11", "impl test 13 failed";

  var r14 := StringSimilarity(3, "11100");
  expect r14 == "111", "impl test 14 failed";

  var r15 := StringSimilarity(6, "10101010101");
  expect r15 == "000000", "impl test 15 failed";

  var r16 := StringSimilarity(4, "0000000");
  expect r16 == "0000", "impl test 16 failed";

  var r17 := StringSimilarity(4, "1111111");
  expect r17 == "1111", "impl test 17 failed";

  var r18 := StringSimilarity(7, "0110100110100");
  expect r18 == "0000000", "impl test 18 failed";

  print "All tests passed\n";
}
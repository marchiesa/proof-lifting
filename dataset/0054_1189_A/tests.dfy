function CountChar(s: string, c: char): int
  decreases |s|
{
  if |s| == 0 then 0
  else CountChar(s[..|s|-1], c) + (if s[|s|-1] == c then 1 else 0)
}

predicate IsGood(s: string)
{
  CountChar(s, '0') != CountChar(s, '1')
}

predicate IsBinaryString(s: string)
{
  forall i | 0 <= i < |s| :: s[i] == '0' || s[i] == '1'
}

function Flatten(parts: seq<string>): string
  decreases |parts|
{
  if |parts| == 0 then ""
  else Flatten(parts[..|parts|-1]) + parts[|parts|-1]
}

predicate AllGood(parts: seq<string>)
{
  forall i | 0 <= i < |parts| :: IsGood(parts[i])
}

// Combined ensures predicate for spec testing
predicate MeetsSpec(s: string, k: int, parts: seq<string>)
{
  k == |parts| &&
  (k == 1 || k == 2) &&
  Flatten(parts) == s &&
  AllGood(parts) &&
  (k == 1 <==> IsGood(s))
}

method KeanuReeves(s: string) returns (k: int, parts: seq<string>)
  requires |s| > 0
  requires IsBinaryString(s)
  ensures k == |parts|
  ensures k == 1 || k == 2
  ensures Flatten(parts) == s
  ensures AllGood(parts)
  ensures k == 1 <==> IsGood(s)
{
  var zeros := 0;
  var ones := 0;
  var i := 0;
  while i < |s|
  {
    if s[i] == '0' {
      zeros := zeros + 1;
    } else {
      ones := ones + 1;
    }
    i := i + 1;
  }
  if zeros != ones {
    k := 1;
    parts := [s];
  } else {
    k := 2;
    parts := [s[..|s| - 1], [s[|s| - 1]]];
  }
}

method Main()
{
  var k: int;
  var parts: seq<string>;

  // ===== SPEC POSITIVE TESTS =====
  // Correct (input, output) pairs satisfy all ensures conditions

  // From positive test 1: s="1", k=1, parts=["1"]
  expect MeetsSpec("1", 1, ["1"]), "spec positive 1";

  // From positive test 2: s="10", k=2, parts=["1","0"]
  expect MeetsSpec("10", 2, ["1", "0"]), "spec positive 2";

  // From positive test 4: s="0101", k=2, parts=["010","1"]
  expect MeetsSpec("0101", 2, ["010", "1"]), "spec positive 3";

  // From positive test 19: s="11", k=1, parts=["11"]
  expect MeetsSpec("11", 1, ["11"]), "spec positive 4";

  // From positive test 20: s="100", k=1, parts=["100"]
  expect MeetsSpec("100", 1, ["100"]), "spec positive 5";

  // From positive test 9: s="010011", k=2, parts=["01001","1"]
  expect MeetsSpec("010011", 2, ["01001", "1"]), "spec positive 6";

  // From positive test 3: s="100011", k=2, parts=["10001","1"]
  expect MeetsSpec("100011", 2, ["10001", "1"]), "spec positive 7";

  // From positive test 10: s="1100010011", k=2, parts=["110001001","1"]
  expect MeetsSpec("1100010011", 2, ["110001001", "1"]), "spec positive 8";

  // ===== SPEC NEGATIVE TESTS =====
  // Wrong outputs must violate at least one ensures condition

  // From negative 1: s="1", wrong k=2, parts=["1"] (k != |parts|)
  expect !MeetsSpec("1", 2, ["1"]), "spec negative 1";

  // From negative 2: s="10", wrong k=3, parts=["1","0"] (k != |parts|, k not in {1,2})
  expect !MeetsSpec("10", 3, ["1", "0"]), "spec negative 2";

  // From negative 4: s="0101", wrong k=3, parts=["010","1"] (k != |parts|)
  expect !MeetsSpec("0101", 3, ["010", "1"]), "spec negative 3";

  // From negative 9: s="010011", wrong k=3, parts=["01001","1"] (k != |parts|)
  expect !MeetsSpec("010011", 3, ["01001", "1"]), "spec negative 4";

  // From negative 10: s="1100010011", wrong k=3, parts=["110001001","1"] (k != |parts|)
  expect !MeetsSpec("1100010011", 3, ["110001001", "1"]), "spec negative 5";

  // From negative 3: s="100011", wrong k=3, parts=["10001","1"] (k != |parts|)
  expect !MeetsSpec("100011", 3, ["10001", "1"]), "spec negative 6";

  // From negative 1 variant: s="1", wrong k=2, parts=["","1"] (k==|parts| but k==1 <==> IsGood fails)
  expect !MeetsSpec("11", 2, ["11"]), "spec negative 7";

  // ===== IMPLEMENTATION TESTS =====

  // Test 1
  k, parts := KeanuReeves("1");
  expect k == 1, "impl test 1: k";
  expect parts == ["1"], "impl test 1: parts";

  // Test 2
  k, parts := KeanuReeves("10");
  expect k == 2, "impl test 2: k";
  expect parts == ["1", "0"], "impl test 2: parts";

  // Test 3
  k, parts := KeanuReeves("100011");
  expect k == 2, "impl test 3: k";
  expect parts == ["10001", "1"], "impl test 3: parts";

  // Test 4
  k, parts := KeanuReeves("0101");
  expect k == 2, "impl test 4: k";
  expect parts == ["010", "1"], "impl test 4: parts";

  // Test 5
  k, parts := KeanuReeves("1101001100");
  expect k == 2, "impl test 5: k";
  expect parts == ["110100110", "0"], "impl test 5: parts";

  // Test 6
  k, parts := KeanuReeves("10010000111011010000111011111010010100001101");
  expect k == 2, "impl test 6: k";
  expect parts == ["1001000011101101000011101111101001010000110", "1"], "impl test 6: parts";

  // Test 7
  k, parts := KeanuReeves("01110111110010110111011110101000110110000111000100111000000101001011111000110011");
  expect k == 1, "impl test 7: k";
  expect parts == ["01110111110010110111011110101000110110000111000100111000000101001011111000110011"], "impl test 7: parts";

  // Test 8
  k, parts := KeanuReeves("0010110000001111110111101011100111101000110011011100100011110001101110000001000010100001011011110001");
  expect k == 2, "impl test 8: k";
  expect parts == ["001011000000111111011110101110011110100011001101110010001111000110111000000100001010000101101111000", "1"], "impl test 8: parts";

  // Test 9
  k, parts := KeanuReeves("010011");
  expect k == 2, "impl test 9: k";
  expect parts == ["01001", "1"], "impl test 9: parts";

  // Test 10
  k, parts := KeanuReeves("1100010011");
  expect k == 2, "impl test 10: k";
  expect parts == ["110001001", "1"], "impl test 10: parts";

  // Test 11
  k, parts := KeanuReeves("101010100101");
  expect k == 2, "impl test 11: k";
  expect parts == ["10101010010", "1"], "impl test 11: parts";

  // Test 12
  k, parts := KeanuReeves("110001101000101");
  expect k == 1, "impl test 12: k";
  expect parts == ["110001101000101"], "impl test 12: parts";

  // Test 13
  k, parts := KeanuReeves("101111001111000110");
  expect k == 1, "impl test 13: k";
  expect parts == ["101111001111000110"], "impl test 13: parts";

  // Test 14
  k, parts := KeanuReeves("10010000010111010111");
  expect k == 2, "impl test 14: k";
  expect parts == ["1001000001011101011", "1"], "impl test 14: parts";

  // Test 15
  k, parts := KeanuReeves("111100110011010001010010100011001101");
  expect k == 2, "impl test 15: k";
  expect parts == ["11110011001101000101001010001100110", "1"], "impl test 15: parts";

  // Test 16
  k, parts := KeanuReeves("101001101111010010111100000111111010111001001");
  expect k == 1, "impl test 16: k";
  expect parts == ["101001101111010010111100000111111010111001001"], "impl test 16: parts";

  // Test 17
  k, parts := KeanuReeves("111101100111001110000000100010100000011011100110001010111010101011111100");
  expect k == 2, "impl test 17: k";
  expect parts == ["11110110011100111000000010001010000001101110011000101011101010101111110", "0"], "impl test 17: parts";

  // Test 18
  k, parts := KeanuReeves("0110110011011111001110000110010010000111111001100001011101101000001011001101100111011111100111101110");
  expect k == 1, "impl test 18: k";
  expect parts == ["0110110011011111001110000110010010000111111001100001011101101000001011001101100111011111100111101110"], "impl test 18: parts";

  // Test 19
  k, parts := KeanuReeves("11");
  expect k == 1, "impl test 19: k";
  expect parts == ["11"], "impl test 19: parts";

  // Test 20
  k, parts := KeanuReeves("100");
  expect k == 1, "impl test 20: k";
  expect parts == ["100"], "impl test 20: parts";

  print "All tests passed\n";
}
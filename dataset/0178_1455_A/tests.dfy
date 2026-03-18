// --- Specification functions ---

function DigitsToNat(s: seq<int>): int
  decreases |s|
{
  if |s| == 0 then 0
  else DigitsToNat(s[..|s|-1]) * 10 + s[|s|-1]
}

function NatToDigits(n: int): seq<int>
  decreases n
{
  if n < 0 then [0]
  else if n < 10 then [n]
  else NatToDigits(n / 10) + [n % 10]
}

function ReverseSeq(s: seq<int>): seq<int>
  decreases |s|
{
  if |s| == 0 then []
  else [s[|s|-1]] + ReverseSeq(s[..|s|-1])
}

function StripLeadingZeros(s: seq<int>): seq<int>
  decreases |s|
{
  if |s| <= 1 then s
  else if s[0] == 0 then StripLeadingZeros(s[1..])
  else s
}

function ReverseDigits(x: int): int
{
  if x < 0 then 0
  else
    var digits := NatToDigits(x);
    var reversed := ReverseSeq(digits);
    var stripped := StripLeadingZeros(reversed);
    DigitsToNat(stripped)
}

function GValue(x: int): int
{
  if x < 1 then 0
  else
    var ffx := ReverseDigits(ReverseDigits(x));
    if ffx == 0 then 0
    else x / ffx
}

function CountDistinctGValues(N: int): int
{
  if N < 1 then 0
  else |set x: int | 1 <= x <= N :: GValue(x)|
}

predicate ValidPositiveDigitSeq(s: seq<int>)
{
  |s| > 0 &&
  s[0] != 0 &&
  (forall i | 0 <= i < |s| :: 0 <= s[i] <= 9)
}

// --- Implementation ---

method StrangeFunctions(n: seq<int>) returns (result: int)
  requires ValidPositiveDigitSeq(n)
  ensures result == CountDistinctGValues(DigitsToNat(n))
{
  result := |n|;
}

method Repeat(d: int, count: int) returns (s: seq<int>)
{
  s := [];
  var i := 0;
  while i < count {
    s := s + [d];
    i := i + 1;
  }
}

method StringToDigits(str: string) returns (s: seq<int>)
{
  s := [];
  var i := 0;
  while i < |str| {
    s := s + [str[i] as int - '0' as int];
    i := i + 1;
  }
}

method Main()
{
  var r: int;
  var n: seq<int>;

  // ========================================
  // SPEC POSITIVE TESTS
  // ensures: result == CountDistinctGValues(DigitsToNat(n))
  // Small inputs only (N <= 19) to keep set comprehension feasible
  // ========================================

  // From Test 6: [1] -> 1 (N=1)
  expect CountDistinctGValues(DigitsToNat([1])) == 1, "spec positive 1";
  // From Test 1 (first case): [4] -> 1 (N=4)
  expect CountDistinctGValues(DigitsToNat([4])) == 1, "spec positive 2";
  // From Test 2: [1,0] -> 2 (N=10)
  expect CountDistinctGValues(DigitsToNat([1,0])) == 2, "spec positive 3";
  // From Test 12: [1,1] -> 2 (N=11)
  expect CountDistinctGValues(DigitsToNat([1,1])) == 2, "spec positive 4";
  // From Test 9: [1,2] -> 2 (N=12)
  expect CountDistinctGValues(DigitsToNat([1,2])) == 2, "spec positive 5";
  // From Test 9: [1,3] -> 2 (N=13)
  expect CountDistinctGValues(DigitsToNat([1,3])) == 2, "spec positive 6";
  // From Test 9: [1,9] -> 2 (N=19)
  expect CountDistinctGValues(DigitsToNat([1,9])) == 2, "spec positive 7";

  // ========================================
  // SPEC NEGATIVE TESTS
  // Verify spec rejects wrong outputs
  // ========================================

  // From Neg 6: [1] correct 1, wrong 2
  expect CountDistinctGValues(DigitsToNat([1])) != 2, "spec negative 1";
  // From Neg 1: [4] correct 1, wrong 2
  expect CountDistinctGValues(DigitsToNat([4])) != 2, "spec negative 2";
  // From Neg 2: [1,0] correct 2, wrong 3
  expect CountDistinctGValues(DigitsToNat([1,0])) != 3, "spec negative 3";
  // From Neg 9: [1,2] correct 2, wrong 3
  expect CountDistinctGValues(DigitsToNat([1,2])) != 3, "spec negative 4";
  // Scaled from Neg 3 (all 9s, off by +1): [9] correct 1, wrong 2
  expect CountDistinctGValues(DigitsToNat([9])) != 2, "spec negative 5";
  // Scaled from Neg 5 (off by +1): [5] correct 1, wrong 2
  expect CountDistinctGValues(DigitsToNat([5])) != 2, "spec negative 6";
  // Scaled from Neg 4 (off by +1): [3] correct 1, wrong 2
  expect CountDistinctGValues(DigitsToNat([3])) != 2, "spec negative 7";
  // Scaled from Neg 8 (off by +1): [7] correct 1, wrong 2
  expect CountDistinctGValues(DigitsToNat([7])) != 2, "spec negative 8";
  // Scaled from Neg 10 (off by +1): [2] correct 1, wrong 2
  expect CountDistinctGValues(DigitsToNat([2])) != 2, "spec negative 9";
  // From Neg 7: [1,0] correct 2, wrong 3
  expect CountDistinctGValues(DigitsToNat([1,0])) != 3, "spec negative 10";

  // ========================================
  // IMPLEMENTATION TESTS
  // ========================================

  // Test 1
  r := StrangeFunctions([4]);
  expect r == 1, "impl test 1.1";
  r := StrangeFunctions([3, 7]);
  expect r == 2, "impl test 1.2";
  r := StrangeFunctions([9, 9, 8, 2, 4, 4, 3, 5, 3]);
  expect r == 9, "impl test 1.3";
  r := StrangeFunctions([1, 0, 0, 0, 0, 0, 0, 0, 0, 7]);
  expect r == 10, "impl test 1.4";
  r := StrangeFunctions([1, 2, 3, 4, 5, 6, 7, 8, 9, 0, 1, 3, 3, 7, 4, 2, 6, 9, 6, 6, 6, 3, 1, 4, 1, 5]);
  expect r == 26, "impl test 1.5";

  // Test 2
  r := StrangeFunctions([1, 0]);
  expect r == 2, "impl test 2";

  // Test 3: 59 nines
  n := Repeat(9, 59);
  r := StrangeFunctions(n);
  expect r == 59, "impl test 3";

  // Test 4
  r := StrangeFunctions([1, 0, 0, 0]);
  expect r == 4, "impl test 4";

  // Test 5
  r := StrangeFunctions([5, 4, 3, 2]);
  expect r == 4, "impl test 5.1";
  r := StrangeFunctions([5, 3, 4, 2]);
  expect r == 4, "impl test 5.2";
  r := StrangeFunctions([2, 4, 3]);
  expect r == 3, "impl test 5.3";

  // Test 6
  r := StrangeFunctions([1]);
  expect r == 1, "impl test 6";

  // Test 7
  r := StrangeFunctions([1, 0]);
  expect r == 2, "impl test 7.1";
  r := StrangeFunctions([1, 0, 0]);
  expect r == 3, "impl test 7.2";

  // Test 8: 94 nines
  n := Repeat(9, 94);
  r := StrangeFunctions(n);
  expect r == 94, "impl test 8";

  // Test 9
  r := StrangeFunctions([1, 2]);
  expect r == 2, "impl test 9.1";
  r := StrangeFunctions([1, 2]);
  expect r == 2, "impl test 9.2";
  r := StrangeFunctions([1, 3]);
  expect r == 2, "impl test 9.3";
  r := StrangeFunctions([1, 4]);
  expect r == 2, "impl test 9.4";
  r := StrangeFunctions([1, 5]);
  expect r == 2, "impl test 9.5";
  r := StrangeFunctions([1, 6]);
  expect r == 2, "impl test 9.6";
  r := StrangeFunctions([1, 7]);
  expect r == 2, "impl test 9.7";
  r := StrangeFunctions([1, 8]);
  expect r == 2, "impl test 9.8";
  r := StrangeFunctions([1, 9]);
  expect r == 2, "impl test 9.9";

  // Test 10
  r := StrangeFunctions([1, 0, 0, 0, 0, 0, 0, 0, 0, 0]);
  expect r == 10, "impl test 10";

  // Test 11: 99 cases of [1] -> 1
  var i := 0;
  while i < 99 {
    r := StrangeFunctions([1]);
    expect r == 1, "impl test 11";
    i := i + 1;
  }

  // Test 12
  r := StrangeFunctions([1, 1]);
  expect r == 2, "impl test 12";

  // Test 13: 10^99 (100 digits)
  n := Repeat(0, 99);
  n := [1] + n;
  r := StrangeFunctions(n);
  expect r == 100, "impl test 13";

  // Test 14: 100 nines
  n := Repeat(9, 100);
  r := StrangeFunctions(n);
  expect r == 100, "impl test 14";

  // Test 15
  r := StrangeFunctions([1, 0, 0]);
  expect r == 3, "impl test 15";

  // Test 16
  n := Repeat(0, 99);
  n := [1] + n;
  r := StrangeFunctions(n);
  expect r == 100, "impl test 16.1";
  n := Repeat(9, 99);
  r := StrangeFunctions(n);
  expect r == 99, "impl test 16.2";

  // Test 17
  n := Repeat(9, 94);
  r := StrangeFunctions(n);
  expect r == 94, "impl test 17.1";

  n := StringToDigits("18888888888888888888888888800000000000000000000000000009999999990000000000000000094494990400000");
  r := StrangeFunctions(n);
  expect r == 95, "impl test 17.2";

  n := Repeat(0, 98);
  n := [1] + n;
  r := StrangeFunctions(n);
  expect r == 99, "impl test 17.3";

  n := Repeat(9, 99);
  r := StrangeFunctions(n);
  expect r == 99, "impl test 17.4";

  n := StringToDigits("1234567899876543210");
  var t := Repeat(0, 54);
  n := n + t;
  r := StrangeFunctions(n);
  expect r == 73, "impl test 17.5";

  // Test 18
  r := StrangeFunctions([1, 1]);
  expect r == 2, "impl test 18.1";
  r := StrangeFunctions([1, 1, 1]);
  expect r == 3, "impl test 18.2";

  // Test 19
  r := StrangeFunctions([8, 6, 2, 7]);
  expect r == 4, "impl test 19";

  // Test 20: 99 nines
  n := Repeat(9, 99);
  r := StrangeFunctions(n);
  expect r == 99, "impl test 20";

  print "All tests passed\n";
}
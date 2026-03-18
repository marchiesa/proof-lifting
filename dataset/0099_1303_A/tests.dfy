predicate IsBinaryString(s: seq<char>)
{
  forall i | 0 <= i < |s| :: s[i] == '0' || s[i] == '1'
}

predicate OnesContiguous(s: seq<char>)
{
  forall i | 0 <= i < |s| ::
    forall j | i < j < |s| ::
      forall k | j < k < |s| ::
        !(s[i] == '1' && s[j] == '0' && s[k] == '1')
}

predicate CanAchieveWithAtMost(s: seq<char>, k: nat)
  decreases k
{
  OnesContiguous(s) ||
  (k > 0 && exists i | 0 <= i < |s| ::
    s[i] == '0' && CanAchieveWithAtMost(s[..i] + s[i+1..], k - 1))
}

predicate IsMinErasures(s: seq<char>, k: nat)
{
  CanAchieveWithAtMost(s, k) &&
  (k == 0 || !CanAchieveWithAtMost(s, k - 1))
}

method ErasingZeroes(s: string) returns (ans: int)
  requires IsBinaryString(s)
  ensures ans >= 0
  ensures IsMinErasures(s, ans as nat)
{
  var l := -1;
  var r := -1;
  var i := 0;
  while i < |s|
  {
    if s[i] == '1' {
      r := i;
      if l == -1 {
        l := i;
      }
    }
    i := i + 1;
  }
  ans := 0;
  if l != -1 {
    i := l;
    while i < r
    {
      if s[i] == '0' {
        ans := ans + 1;
      }
      i := i + 1;
    }
  }
}

method Main()
{
  // === SPEC POSITIVE TESTS ===
  // Small-input equivalents testing IsMinErasures (the top-level ensures predicate)
  expect IsMinErasures("0", 0), "spec positive 1";       // from test 2: "0" -> 0
  expect IsMinErasures("1", 0), "spec positive 2";       // from test 1: "1111000" -> 0 (scaled)
  expect IsMinErasures("11", 0), "spec positive 3";      // from test 4: "01111110" -> 0 (scaled)
  expect IsMinErasures("01", 0), "spec positive 4";      // from test 4: contiguous ones, 0 erasures
  expect IsMinErasures("101", 1), "spec positive 5";     // from test 3: "01010" -> 1 (scaled)
  expect IsMinErasures("10", 0), "spec positive 6";      // from test 1: contiguous ones, 0 erasures
  expect IsMinErasures("010", 0), "spec positive 7";     // from test 5: single one, already contiguous

  // === SPEC NEGATIVE TESTS ===
  // Small-input equivalents testing that wrong outputs are rejected
  expect !IsMinErasures("101", 2), "spec negative 1";    // from neg 1: wrong=3 (too high), scaled
  expect !IsMinErasures("0", 1), "spec negative 2";      // from neg 2: wrong=1, correct=0
  expect !IsMinErasures("101", 0), "spec negative 3";    // from neg 3: wrong=2 (too low), scaled
  expect !IsMinErasures("11", 1), "spec negative 4";     // from neg 4: wrong=1, correct=0
  expect !IsMinErasures("01", 1), "spec negative 5";     // from neg 5: wrong=2 (too high), scaled

  // === IMPLEMENTATION TESTS ===
  // Test 1
  var r1 := ErasingZeroes("010011");
  expect r1 == 2, "impl test 1 failed";

  var r2 := ErasingZeroes("0");
  expect r2 == 0, "impl test 2 failed";

  var r3 := ErasingZeroes("1111000");
  expect r3 == 0, "impl test 3 failed";

  // Test 2
  var r4 := ErasingZeroes("0");
  expect r4 == 0, "impl test 4 failed";

  var r5 := ErasingZeroes("0");
  expect r5 == 0, "impl test 5 failed";

  var r6 := ErasingZeroes("0");
  expect r6 == 0, "impl test 6 failed";

  var r7 := ErasingZeroes("0");
  expect r7 == 0, "impl test 7 failed";

  var r8 := ErasingZeroes("0");
  expect r8 == 0, "impl test 8 failed";

  var r9 := ErasingZeroes("0");
  expect r9 == 0, "impl test 9 failed";

  var r10 := ErasingZeroes("0");
  expect r10 == 0, "impl test 10 failed";

  // Test 3
  var r11 := ErasingZeroes("01010");
  expect r11 == 1, "impl test 11 failed";

  var r12 := ErasingZeroes("0");
  expect r12 == 0, "impl test 12 failed";

  // Test 4
  var r13 := ErasingZeroes("01111110");
  expect r13 == 0, "impl test 13 failed";

  // Test 5
  var r14 := ErasingZeroes("00101111100");
  expect r14 == 1, "impl test 14 failed";

  print "All tests passed\n";
}
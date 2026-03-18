method ErasingZeroes(s: string) returns (ans: int)
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
  // Test 1
  var r1 := ErasingZeroes("010011");
  expect r1 == 2, "Test 1a failed";

  var r2 := ErasingZeroes("0");
  expect r2 == 0, "Test 1b failed";

  var r3 := ErasingZeroes("1111000");
  expect r3 == 0, "Test 1c failed";

  // Test 2
  var r4 := ErasingZeroes("0");
  expect r4 == 0, "Test 2a failed";

  var r5 := ErasingZeroes("0");
  expect r5 == 0, "Test 2b failed";

  var r6 := ErasingZeroes("0");
  expect r6 == 0, "Test 2c failed";

  var r7 := ErasingZeroes("0");
  expect r7 == 0, "Test 2d failed";

  var r8 := ErasingZeroes("0");
  expect r8 == 0, "Test 2e failed";

  var r9 := ErasingZeroes("0");
  expect r9 == 0, "Test 2f failed";

  var r10 := ErasingZeroes("0");
  expect r10 == 0, "Test 2g failed";

  // Test 3
  var r11 := ErasingZeroes("01010");
  expect r11 == 1, "Test 3a failed";

  var r12 := ErasingZeroes("0");
  expect r12 == 0, "Test 3b failed";

  // Test 4
  var r13 := ErasingZeroes("01111110");
  expect r13 == 0, "Test 4 failed";

  // Test 5
  var r14 := ErasingZeroes("00101111100");
  expect r14 == 1, "Test 5 failed";

  print "All tests passed\n";
}
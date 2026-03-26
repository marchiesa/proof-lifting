method SubstringRemovalGame(s: string) returns (aliceScore: int)
{
  var n := |s|;
  var i := 0;
  var b: seq<int> := [];

  // Find runs of '1's
  while i < n
  {
    var j := i;
    while j < n && s[i] == s[j]
    {
      j := j + 1;
    }
    if s[i] == '1' {
      b := b + [j - i];
    }
    i := j;
  }

  // Sort descending (selection sort)
  var arr := b;
  var len := |arr|;
  var k := 0;
  while k < len
  {
    var maxIdx := k;
    var m := k + 1;
    while m < len
    {
      if arr[m] > arr[maxIdx] {
        maxIdx := m;
      }
      m := m + 1;
    }
    if maxIdx != k {
      var temp := arr[k];
      arr := arr[k := arr[maxIdx]][maxIdx := temp];
    }
    k := k + 1;
  }

  // Sum every other element (Alice's picks)
  aliceScore := 0;
  var idx := 0;
  while idx < |arr|
  {
    aliceScore := aliceScore + arr[idx];
    idx := idx + 2;
  }
}

method Main()
{
  // Test 1
  var r := SubstringRemovalGame("01111001");
  expect r == 4, "Test 1a failed";
  r := SubstringRemovalGame("0000");
  expect r == 0, "Test 1b failed";
  r := SubstringRemovalGame("111111");
  expect r == 6, "Test 1c failed";
  r := SubstringRemovalGame("101010101");
  expect r == 3, "Test 1d failed";
  r := SubstringRemovalGame("011011110111");
  expect r == 6, "Test 1e failed";

  // Test 2
  r := SubstringRemovalGame("01");
  expect r == 1, "Test 2 failed";

  // Test 3
  r := SubstringRemovalGame("1");
  expect r == 1, "Test 3 failed";

  // Test 4
  r := SubstringRemovalGame("0");
  expect r == 0, "Test 4 failed";

  // Test 5
  r := SubstringRemovalGame("1100110");
  expect r == 2, "Test 5 failed";

  // Test 6
  r := SubstringRemovalGame("111");
  expect r == 3, "Test 6a failed";
  r := SubstringRemovalGame("000");
  expect r == 0, "Test 6b failed";
  r := SubstringRemovalGame("1010");
  expect r == 1, "Test 6c failed";

  // Test 7
  r := SubstringRemovalGame("01010");
  expect r == 1, "Test 7a failed";
  r := SubstringRemovalGame("11011");
  expect r == 2, "Test 7b failed";

  // Test 8
  r := SubstringRemovalGame("0001000");
  expect r == 1, "Test 8 failed";

  // Test 9
  r := SubstringRemovalGame("1");
  expect r == 1, "Test 9a failed";
  r := SubstringRemovalGame("0");
  expect r == 0, "Test 9b failed";
  r := SubstringRemovalGame("10");
  expect r == 1, "Test 9c failed";
  r := SubstringRemovalGame("01");
  expect r == 1, "Test 9d failed";

  // Test 10
  r := SubstringRemovalGame("1111111");
  expect r == 7, "Test 10a failed";
  r := SubstringRemovalGame("0101010");
  expect r == 2, "Test 10b failed";

  // Test 11
  r := SubstringRemovalGame("110");
  expect r == 2, "Test 11a failed";
  r := SubstringRemovalGame("001");
  expect r == 1, "Test 11b failed";
  r := SubstringRemovalGame("1110");
  expect r == 3, "Test 11c failed";
  r := SubstringRemovalGame("00100");
  expect r == 1, "Test 11d failed";
  r := SubstringRemovalGame("10101");
  expect r == 2, "Test 11e failed";

  print "All tests passed\n";
}
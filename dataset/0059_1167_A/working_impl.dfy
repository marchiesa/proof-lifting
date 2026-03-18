method TelephoneNumber(s: string, n: int) returns (result: bool)
{
  var i := 0;
  while i < n - 10
  {
    if s[i] == '8' {
      return true;
    }
    i := i + 1;
  }
  return false;
}

method Main()
{
  // Test 1, case 1: n=13, s="7818005553535" → YES (true)
  var r1 := TelephoneNumber("7818005553535", 13);
  expect r1 == true, "Test 1.1 failed: expected true";

  // Test 1, case 2: n=11, s="31415926535" → NO (false)
  var r2 := TelephoneNumber("31415926535", 11);
  expect r2 == false, "Test 1.2 failed: expected false";

  // Test 2: n=11, s="80000000000" → YES (true)
  var r3 := TelephoneNumber("80000000000", 11);
  expect r3 == true, "Test 2 failed: expected true";

  // Test 3: n=11, s="83583640644" → YES (true)
  var r4 := TelephoneNumber("83583640644", 11);
  expect r4 == true, "Test 3 failed: expected true";

  print "All tests passed\n";
}
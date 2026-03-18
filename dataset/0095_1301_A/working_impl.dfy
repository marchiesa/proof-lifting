method ThreeStrings(a: string, b: string, c: string) returns (result: bool)
{
  var i := 0;
  while i < |a|
  {
    if a[i] != c[i] && b[i] != c[i] {
      return false;
    }
    i := i + 1;
  }
  return true;
}

method Main()
{
  // Test 1, case 1
  var r1 := ThreeStrings("aaa", "bbb", "ccc");
  expect r1 == false, "Test 1.1 failed";

  // Test 1, case 2
  var r2 := ThreeStrings("abc", "bca", "bca");
  expect r2 == true, "Test 1.2 failed";

  // Test 1, case 3
  var r3 := ThreeStrings("aabb", "bbaa", "baba");
  expect r3 == true, "Test 1.3 failed";

  // Test 1, case 4
  var r4 := ThreeStrings("imi", "mii", "iim");
  expect r4 == false, "Test 1.4 failed";

  // Test 2, case 1
  var r5 := ThreeStrings("ab", "ab", "bb");
  expect r5 == false, "Test 2.1 failed";

  print "All tests passed\n";
}
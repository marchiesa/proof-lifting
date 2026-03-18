method Prefixes(s: seq<char>) returns (ops: int, result: seq<char>)
{
  ops := 0;
  result := [];
  var i := 0;
  while i < |s|
  {
    if s[i] == s[i + 1] {
      result := result + ['a', 'b'];
      ops := ops + 1;
    } else {
      result := result + [s[i], s[i + 1]];
    }
    i := i + 2;
  }
}

method Main()
{
  // Test 1
  var ops1, res1 := Prefixes(['b', 'b', 'b', 'b']);
  expect ops1 == 2, "Test 1: expected ops=2";
  expect res1 == ['a', 'b', 'a', 'b'], "Test 1: expected result=abab";

  // Test 2
  var ops2, res2 := Prefixes(['a', 'b', 'a', 'b', 'a', 'b']);
  expect ops2 == 0, "Test 2: expected ops=0";
  expect res2 == ['a', 'b', 'a', 'b', 'a', 'b'], "Test 2: expected result=ababab";

  // Test 3
  var ops3, res3 := Prefixes(['a', 'a']);
  expect ops3 == 1, "Test 3: expected ops=1";
  expect res3 == ['a', 'b'], "Test 3: expected result=ab";

  // Test 4
  var ops4, res4 := Prefixes(['b', 'b', 'b', 'b', 'b', 'a']);
  expect ops4 == 2, "Test 4: expected ops=2";
  expect res4 == ['a', 'b', 'a', 'b', 'b', 'a'], "Test 4: expected result=ababba";

  // Test 5
  var ops5, res5 := Prefixes(['b', 'b', 'b', 'a', 'b', 'b', 'b', 'a']);
  expect ops5 == 2, "Test 5: expected ops=2";
  expect res5 == ['a', 'b', 'b', 'a', 'a', 'b', 'b', 'a'], "Test 5: expected result=abbaabba";

  // Test 6
  var ops6, res6 := Prefixes(['b', 'b', 'a', 'b', 'b', 'b', 'a', 'a']);
  expect ops6 == 3, "Test 6: expected ops=3";
  expect res6 == ['a', 'b', 'a', 'b', 'a', 'b', 'a', 'b'], "Test 6: expected result=abababab";

  print "All tests passed\n";
}
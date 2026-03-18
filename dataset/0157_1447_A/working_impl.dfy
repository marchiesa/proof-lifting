method AddCandies(n: int) returns (m: int, a: seq<int>)
{
  m := n;
  a := [];
  var i := 1;
  while i <= n {
    a := a + [i];
    i := i + 1;
  }
}

method MakeSeq1ToN(n: int) returns (s: seq<int>)
{
  s := [];
  var i := 1;
  while i <= n {
    s := s + [i];
    i := i + 1;
  }
}

method CheckAddCandies(n: int, testName: string)
{
  var m, a := AddCandies(n);
  var expected := MakeSeq1ToN(n);
  expect m == n, testName + ": m mismatch";
  expect a == expected, testName + ": a mismatch";
}

method Main() {
  // Test 1: n=2, n=3
  CheckAddCandies(2, "Test 1 n=2");
  CheckAddCandies(3, "Test 1 n=3");

  // Test 2: n=100, then n=2..100
  CheckAddCandies(100, "Test 2 n=100");
  var i := 2;
  while i <= 100 {
    CheckAddCandies(i, "Test 2 loop");
    i := i + 1;
  }

  // Test 3: n=2
  CheckAddCandies(2, "Test 3 n=2");

  // Test 4: n=5
  CheckAddCandies(5, "Test 4 n=5");

  // Test 5: n=100
  CheckAddCandies(100, "Test 5 n=100");

  // Test 6: n=2,3,4
  CheckAddCandies(2, "Test 6 n=2");
  CheckAddCandies(3, "Test 6 n=3");
  CheckAddCandies(4, "Test 6 n=4");

  // Test 7: n=10,20,30,40,50
  CheckAddCandies(10, "Test 7 n=10");
  CheckAddCandies(20, "Test 7 n=20");
  CheckAddCandies(30, "Test 7 n=30");
  CheckAddCandies(40, "Test 7 n=40");
  CheckAddCandies(50, "Test 7 n=50");

  // Test 8: n=7
  CheckAddCandies(7, "Test 8 n=7");

  // Test 9: n=3, n=6
  CheckAddCandies(3, "Test 9 n=3");
  CheckAddCandies(6, "Test 9 n=6");

  // Test 10: n=2,5,11,99
  CheckAddCandies(2, "Test 10 n=2");
  CheckAddCandies(5, "Test 10 n=5");
  CheckAddCandies(11, "Test 10 n=11");
  CheckAddCandies(99, "Test 10 n=99");

  // Test 11: n=50
  CheckAddCandies(50, "Test 11 n=50");

  // Test 12: n=2,3,4,5,6,7
  CheckAddCandies(2, "Test 12 n=2");
  CheckAddCandies(3, "Test 12 n=3");
  CheckAddCandies(4, "Test 12 n=4");
  CheckAddCandies(5, "Test 12 n=5");
  CheckAddCandies(6, "Test 12 n=6");
  CheckAddCandies(7, "Test 12 n=7");

  print "All tests passed\n";
}
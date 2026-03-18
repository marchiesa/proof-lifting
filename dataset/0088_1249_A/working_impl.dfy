method YetAnotherDividingIntoTeams(a: seq<int>) returns (teams: int)
{
  var b := new int[102];
  var i := 0;
  while i < 102 {
    b[i] := 0;
    i := i + 1;
  }
  i := 0;
  while i < |a| {
    if 0 <= a[i] < 102 {
      b[a[i]] := b[a[i]] + 1;
    }
    i := i + 1;
  }
  var flag := false;
  i := 1;
  while i <= 100 {
    if b[i] == 1 && (b[i + 1] == 1 || b[i - 1] == 1) {
      flag := true;
    }
    i := i + 1;
  }
  if flag {
    teams := 2;
  } else {
    teams := 1;
  }
}

method Main()
{
  var r: int;

  // Test 1
  r := YetAnotherDividingIntoTeams([2, 10, 1, 20]);
  expect r == 2, "Test 1.1 failed";
  r := YetAnotherDividingIntoTeams([3, 6]);
  expect r == 1, "Test 1.2 failed";
  r := YetAnotherDividingIntoTeams([2, 3, 4, 99, 100]);
  expect r == 2, "Test 1.3 failed";
  r := YetAnotherDividingIntoTeams([42]);
  expect r == 1, "Test 1.4 failed";

  // Test 2
  r := YetAnotherDividingIntoTeams([100]);
  expect r == 1, "Test 2.1 failed";

  // Test 3
  r := YetAnotherDividingIntoTeams([3, 4, 1, 5, 2]);
  expect r == 2, "Test 3.1 failed";
  r := YetAnotherDividingIntoTeams([2, 1]);
  expect r == 2, "Test 3.2 failed";
  r := YetAnotherDividingIntoTeams([4, 1, 3, 2]);
  expect r == 2, "Test 3.3 failed";
  r := YetAnotherDividingIntoTeams([2, 3, 1, 5, 4]);
  expect r == 2, "Test 3.4 failed";
  r := YetAnotherDividingIntoTeams([1, 2]);
  expect r == 2, "Test 3.5 failed";
  r := YetAnotherDividingIntoTeams([1, 2, 3, 4]);
  expect r == 2, "Test 3.6 failed";
  r := YetAnotherDividingIntoTeams([1, 2]);
  expect r == 2, "Test 3.7 failed";
  r := YetAnotherDividingIntoTeams([3, 4, 2, 1]);
  expect r == 2, "Test 3.8 failed";
  r := YetAnotherDividingIntoTeams([3, 2, 1]);
  expect r == 2, "Test 3.9 failed";
  r := YetAnotherDividingIntoTeams([1]);
  expect r == 1, "Test 3.10 failed";

  // Test 4
  r := YetAnotherDividingIntoTeams([1, 31]);
  expect r == 1, "Test 4.1 failed";

  // Test 5
  r := YetAnotherDividingIntoTeams([1]);
  expect r == 1, "Test 5.1 failed";
  r := YetAnotherDividingIntoTeams([1]);
  expect r == 1, "Test 5.2 failed";
  r := YetAnotherDividingIntoTeams([1]);
  expect r == 1, "Test 5.3 failed";
  r := YetAnotherDividingIntoTeams([2, 1, 4, 3]);
  expect r == 2, "Test 5.4 failed";
  r := YetAnotherDividingIntoTeams([1, 3, 2]);
  expect r == 2, "Test 5.5 failed";
  r := YetAnotherDividingIntoTeams([1]);
  expect r == 1, "Test 5.6 failed";
  r := YetAnotherDividingIntoTeams([1, 2, 3]);
  expect r == 2, "Test 5.7 failed";
  r := YetAnotherDividingIntoTeams([1, 4, 2, 5, 3]);
  expect r == 2, "Test 5.8 failed";
  r := YetAnotherDividingIntoTeams([4, 5, 2, 3, 1]);
  expect r == 2, "Test 5.9 failed";
  r := YetAnotherDividingIntoTeams([4, 2, 3, 1]);
  expect r == 2, "Test 5.10 failed";

  // Test 6
  r := YetAnotherDividingIntoTeams([3, 5, 7]);
  expect r == 1, "Test 6.1 failed";

  // Test 7
  r := YetAnotherDividingIntoTeams([99, 97]);
  expect r == 1, "Test 7.1 failed";

  print "All tests passed\n";
}
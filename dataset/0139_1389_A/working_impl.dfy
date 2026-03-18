method LCMProblem(l: int, r: int) returns (x: int, y: int)
{
  if l * 2 > r {
    return -1, -1;
  } else {
    return l, l * 2;
  }
}

method Main()
{
  // Test 1
  var x1, y1 := LCMProblem(1, 1337);
  expect x1 == 1 && y1 == 2, "Test 1.1 failed";

  var x2, y2 := LCMProblem(13, 69);
  expect x2 == 13 && y2 == 26, "Test 1.2 failed";

  var x3, y3 := LCMProblem(2, 4);
  expect x3 == 2 && y3 == 4, "Test 1.3 failed";

  var x4, y4 := LCMProblem(88, 89);
  expect x4 == -1 && y4 == -1, "Test 1.4 failed";

  // Test 2
  var x5, y5 := LCMProblem(55556, 55557);
  expect x5 == -1 && y5 == -1, "Test 2 failed";

  // Test 3 (5 repeated cases: l=2, r=4 -> 2, 4)
  var i := 0;
  while i < 5 {
    var a, b := LCMProblem(2, 4);
    expect a == 2 && b == 4, "Test 3 failed";
    i := i + 1;
  }

  // Test 4
  var x6, y6 := LCMProblem(78788, 157576);
  expect x6 == 78788 && y6 == 157576, "Test 4 failed";

  // Test 5
  var x7, y7 := LCMProblem(8743, 17489);
  expect x7 == 8743 && y7 == 17486, "Test 5 failed";

  // Test 6
  var x8, y8 := LCMProblem(96777, 19555557);
  expect x8 == 96777 && y8 == 193554, "Test 6 failed";

  // Test 7
  var x9, y9 := LCMProblem(1000003, 100000000);
  expect x9 == 1000003 && y9 == 2000006, "Test 7 failed";

  // Test 8
  var x10, y10 := LCMProblem(80000000, 160000000);
  expect x10 == 80000000 && y10 == 160000000, "Test 8 failed";

  // Test 9 (69 repeated cases: l=1, r=2 -> 1, 2)
  var j := 0;
  while j < 69 {
    var a, b := LCMProblem(1, 2);
    expect a == 1 && b == 2, "Test 9 failed";
    j := j + 1;
  }

  print "All tests passed\n";
}
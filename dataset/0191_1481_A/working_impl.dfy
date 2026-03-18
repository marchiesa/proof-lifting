method CountChar(s: string, c: char) returns (count: int)
{
  count := 0;
  var i := 0;
  while i < |s|
  {
    if s[i] == c {
      count := count + 1;
    }
    i := i + 1;
  }
}

method SpaceNavigation(px: int, py: int, s: string) returns (result: bool)
{
  var p := true;
  var rc := CountChar(s, 'R');
  var lc := CountChar(s, 'L');
  var uc := CountChar(s, 'U');
  var dc := CountChar(s, 'D');
  if px > 0 && rc < px { p := false; }
  if px < 0 && lc < -px { p := false; }
  if py > 0 && uc < py { p := false; }
  if py < 0 && dc < -py { p := false; }
  return p;
}

method Main()
{
  var r: bool;

  // Test 1
  r := SpaceNavigation(10, 5, "RRRRRRRRRRUUUUU");
  expect r == true, "Test 1.1 failed";

  r := SpaceNavigation(1, 1, "UDDDRLLL");
  expect r == true, "Test 1.2 failed";

  r := SpaceNavigation(-3, -5, "LDLDLDDDR");
  expect r == true, "Test 1.3 failed";

  r := SpaceNavigation(1, 2, "LLLLUU");
  expect r == false, "Test 1.4 failed";

  r := SpaceNavigation(3, -2, "RDULRLLDR");
  expect r == true, "Test 1.5 failed";

  r := SpaceNavigation(-1, 6, "RUDURUUUUR");
  expect r == false, "Test 1.6 failed";

  // Test 2
  r := SpaceNavigation(1, 1, "RU");
  expect r == true, "Test 2.1 failed";

  r := SpaceNavigation(-1, -1, "LD");
  expect r == true, "Test 2.2 failed";

  r := SpaceNavigation(2, 3, "RRUUU");
  expect r == true, "Test 2.3 failed";

  // Test 3
  r := SpaceNavigation(5, 0, "RRRRRLLL");
  expect r == true, "Test 3.1 failed";

  // Test 4
  r := SpaceNavigation(0, 3, "UUUDDUU");
  expect r == true, "Test 4.1 failed";

  // Test 5
  r := SpaceNavigation(-2, -3, "LLDDD");
  expect r == true, "Test 5.1 failed";

  r := SpaceNavigation(3, 3, "RRRUUU");
  expect r == true, "Test 5.2 failed";

  // Test 6
  r := SpaceNavigation(1, 1, "DDDDDDDDDD");
  expect r == false, "Test 6.1 failed";

  // Test 7
  r := SpaceNavigation(-1, 0, "RRRLL");
  expect r == true, "Test 7.1 failed";

  r := SpaceNavigation(0, -2, "UDDDD");
  expect r == true, "Test 7.2 failed";

  // Test 8
  r := SpaceNavigation(4, -3, "RRRRDDDUUL");
  expect r == true, "Test 8.1 failed";

  // Test 9
  r := SpaceNavigation(1, 0, "R");
  expect r == true, "Test 9.1 failed";

  r := SpaceNavigation(0, 1, "U");
  expect r == true, "Test 9.2 failed";

  r := SpaceNavigation(-1, -1, "LD");
  expect r == true, "Test 9.3 failed";

  // Test 10
  r := SpaceNavigation(-3, 2, "LLLRRUUDD");
  expect r == true, "Test 10.1 failed";

  // Test 11
  r := SpaceNavigation(2, -1, "RRDDLUU");
  expect r == true, "Test 11.1 failed";

  r := SpaceNavigation(-4, 0, "LLLLRR");
  expect r == true, "Test 11.2 failed";

  print "All tests passed\n";
}
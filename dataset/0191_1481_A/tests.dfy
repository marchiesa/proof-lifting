// --- Formal Specification ---

function DeltaX(c: char): int {
  if c == 'R' then 1 else if c == 'L' then -1 else 0
}

function DeltaY(c: char): int {
  if c == 'U' then 1 else if c == 'D' then -1 else 0
}

predicate CanReachBySubseq(s: string, px: int, py: int)
  decreases |s|
{
  if px == 0 && py == 0 then
    true
  else if |s| == 0 then
    false
  else
    CanReachBySubseq(s[..|s|-1], px, py)
    || CanReachBySubseq(s[..|s|-1], px - DeltaX(s[|s|-1]), py - DeltaY(s[|s|-1]))
}

// --- Implementation ---

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
  ensures result == CanReachBySubseq(s, px, py)
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
  // ====== SPEC POSITIVE TESTS ======
  // Small inputs (length 1-3) testing CanReachBySubseq matches correct output

  // From Test 9.1: (1, 0, "R") -> true
  expect CanReachBySubseq("R", 1, 0) == true, "spec positive 1";

  // From Test 9.2: (0, 1, "U") -> true
  expect CanReachBySubseq("U", 0, 1) == true, "spec positive 2";

  // From Test 2.2/9.3: (-1, -1, "LD") -> true
  expect CanReachBySubseq("LD", -1, -1) == true, "spec positive 3";

  // From Test 2.1: (1, 1, "RU") -> true
  expect CanReachBySubseq("RU", 1, 1) == true, "spec positive 4";

  // Scaled from Test 6.1: (1, 1, "DD") -> false
  expect CanReachBySubseq("DD", 1, 1) == false, "spec positive 5";

  // Scaled from Test 3.1: (1, 0, "RL") -> true
  expect CanReachBySubseq("RL", 1, 0) == true, "spec positive 6";

  // Scaled from Test 1.4: (1, 1, "LL") -> false
  expect CanReachBySubseq("LL", 1, 1) == false, "spec positive 7";

  // Scaled from Test 1.5: (1, -1, "RD") -> true
  expect CanReachBySubseq("RD", 1, -1) == true, "spec positive 8";

  // Scaled from Test 4.1: (0, 1, "UD") -> true
  expect CanReachBySubseq("UD", 0, 1) == true, "spec positive 9";

  // Scaled from Test 10.1: (-1, 1, "LU") -> true
  expect CanReachBySubseq("LU", -1, 1) == true, "spec positive 10";

  // Scaled from Test 1.6: (-1, 2, "RU") -> false
  expect CanReachBySubseq("RU", -1, 2) == false, "spec positive 11";

  // Scaled from Test 8.1: (1, -1, "RDU") -> true
  expect CanReachBySubseq("RDU", 1, -1) == true, "spec positive 12";

  // ====== SPEC NEGATIVE TESTS ======
  // Wrong output must disagree with CanReachBySubseq

  // Neg 9 scaled (sub-case 3): (-1,-1,"LD") correct=true, wrong=false
  expect false != CanReachBySubseq("LD", -1, -1), "spec negative 1";

  // Neg 6 scaled: (1,1,"DD") correct=false, wrong=true
  expect true != CanReachBySubseq("DD", 1, 1), "spec negative 2";

  // Neg 3 scaled: (1,0,"RL") correct=true, wrong=false
  expect false != CanReachBySubseq("RL", 1, 0), "spec negative 3";

  // Neg 4 scaled: (0,1,"UD") correct=true, wrong=false
  expect false != CanReachBySubseq("UD", 0, 1), "spec negative 4";

  // Neg 8 scaled: (1,-1,"RD") correct=true, wrong=false
  expect false != CanReachBySubseq("RD", 1, -1), "spec negative 5";

  // Neg 10 scaled: (-1,1,"LU") correct=true, wrong=false
  expect false != CanReachBySubseq("LU", -1, 1), "spec negative 6";

  // Neg 1 scaled: (-1,2,"RU") correct=false, wrong=true
  expect true != CanReachBySubseq("RU", -1, 2), "spec negative 7";

  // Neg 2 scaled: (1,1,"RU") correct=true, wrong=false
  expect false != CanReachBySubseq("RU", 1, 1), "spec negative 8";

  // Neg 5 scaled: (1,1,"RUL") correct=true, wrong=false
  expect false != CanReachBySubseq("RUL", 1, 1), "spec negative 9";

  // Neg 7 scaled: (0,-1,"UD") correct=true, wrong=false
  expect false != CanReachBySubseq("UD", 0, -1), "spec negative 10";

  // ====== IMPLEMENTATION TESTS ======
  var r: bool;

  // Test 1
  r := SpaceNavigation(10, 5, "RRRRRRRRRRUUUUU");
  expect r == true, "impl test 1.1 failed";

  r := SpaceNavigation(1, 1, "UDDDRLLL");
  expect r == true, "impl test 1.2 failed";

  r := SpaceNavigation(-3, -5, "LDLDLDDDR");
  expect r == true, "impl test 1.3 failed";

  r := SpaceNavigation(1, 2, "LLLLUU");
  expect r == false, "impl test 1.4 failed";

  r := SpaceNavigation(3, -2, "RDULRLLDR");
  expect r == true, "impl test 1.5 failed";

  r := SpaceNavigation(-1, 6, "RUDURUUUUR");
  expect r == false, "impl test 1.6 failed";

  // Test 2
  r := SpaceNavigation(1, 1, "RU");
  expect r == true, "impl test 2.1 failed";

  r := SpaceNavigation(-1, -1, "LD");
  expect r == true, "impl test 2.2 failed";

  r := SpaceNavigation(2, 3, "RRUUU");
  expect r == true, "impl test 2.3 failed";

  // Test 3
  r := SpaceNavigation(5, 0, "RRRRRLLL");
  expect r == true, "impl test 3.1 failed";

  // Test 4
  r := SpaceNavigation(0, 3, "UUUDDUU");
  expect r == true, "impl test 4.1 failed";

  // Test 5
  r := SpaceNavigation(-2, -3, "LLDDD");
  expect r == true, "impl test 5.1 failed";

  r := SpaceNavigation(3, 3, "RRRUUU");
  expect r == true, "impl test 5.2 failed";

  // Test 6
  r := SpaceNavigation(1, 1, "DDDDDDDDDD");
  expect r == false, "impl test 6.1 failed";

  // Test 7
  r := SpaceNavigation(-1, 0, "RRRLL");
  expect r == true, "impl test 7.1 failed";

  r := SpaceNavigation(0, -2, "UDDDD");
  expect r == true, "impl test 7.2 failed";

  // Test 8
  r := SpaceNavigation(4, -3, "RRRRDDDUUL");
  expect r == true, "impl test 8.1 failed";

  // Test 9
  r := SpaceNavigation(1, 0, "R");
  expect r == true, "impl test 9.1 failed";

  r := SpaceNavigation(0, 1, "U");
  expect r == true, "impl test 9.2 failed";

  r := SpaceNavigation(-1, -1, "LD");
  expect r == true, "impl test 9.3 failed";

  // Test 10
  r := SpaceNavigation(-3, 2, "LLLRRUUDD");
  expect r == true, "impl test 10.1 failed";

  // Test 11
  r := SpaceNavigation(2, -1, "RRDDLUU");
  expect r == true, "impl test 11.1 failed";

  r := SpaceNavigation(-4, 0, "LLLLRR");
  expect r == true, "impl test 11.2 failed";

  print "All tests passed\n";
}
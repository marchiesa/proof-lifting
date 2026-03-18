datatype Command = North | East | South | West | Stay

function IntToCommand(i: int): Command
  requires 0 <= i <= 4
{
  if i == 0 then North
  else if i == 1 then East
  else if i == 2 then South
  else if i == 3 then West
  else Stay
}

function DeltaX(cmd: Command): int {
  match cmd
  case North => 0
  case East => 1
  case South => 0
  case West => -1
  case Stay => 0
}

function DeltaY(cmd: Command): int {
  match cmd
  case North => 1
  case East => 0
  case South => -1
  case West => 0
  case Stay => 0
}

predicate ReachableIn(posX: int, posY: int, targetX: int, targetY: int, steps: int, lastCmd: int)
  decreases if steps > 0 then steps else 0
{
  if steps < 0 then false
  else if steps == 0 then posX == targetX && posY == targetY
  else
    exists c | 0 <= c <= 4 :: c != lastCmd &&
      ReachableIn(posX + DeltaX(IntToCommand(c)), posY + DeltaY(IntToCommand(c)),
                  targetX, targetY, steps - 1, c)
}

predicate IsMinCommands(x: int, y: int, n: int) {
  n >= 0 &&
  ReachableIn(0, 0, x, y, n, -1) &&
  forall k | 0 <= k < n :: !ReachableIn(0, 0, x, y, k, -1)
}

method RobotProgram(x: int, y: int) returns (commands: int)
  requires x >= 0 && y >= 0
  ensures IsMinCommands(x, y, commands)
{
  var mn := if x < y then x else y;
  var diff := if x > y then x - y else y - x;
  var extra := diff * 2 - 1;
  if extra < 0 { extra := 0; }
  commands := mn * 2 + extra;
}

method Main()
{
  var r: int;

  // ===== SPEC POSITIVE TESTS =====
  // IsMinCommands(x, y, correct_n) should hold for small inputs
  expect IsMinCommands(0, 0, 0), "spec positive 1: (0,0)->0";
  expect IsMinCommands(0, 1, 1), "spec positive 2: (0,1)->1";
  expect IsMinCommands(1, 0, 1), "spec positive 3: (1,0)->1";
  expect IsMinCommands(1, 1, 2), "spec positive 4: (1,1)->2";
  expect IsMinCommands(0, 2, 3), "spec positive 5: (0,2)->3";
  expect IsMinCommands(1, 2, 3), "spec positive 6: (1,2)->3";
  expect IsMinCommands(2, 0, 3), "spec positive 7: (2,0)->3";
  expect IsMinCommands(2, 1, 3), "spec positive 8: (2,1)->3";

  // ===== SPEC NEGATIVE TESTS =====
  // IsMinCommands(x, y, wrong_n) should NOT hold
  // Neg 1: (5,5)->11 wrong, scaled to (1,1)->3 wrong (correct 2)
  expect !IsMinCommands(1, 1, 3), "spec negative 1: (1,1) with wrong 3";
  // Neg 2: (0,0)->1 wrong (correct 0), already small
  expect !IsMinCommands(0, 0, 1), "spec negative 2: (0,0) with wrong 1";
  // Neg 3: (999,899)->1998 wrong, scaled to (0,1)->2 wrong (correct 1)
  expect !IsMinCommands(0, 1, 2), "spec negative 3: (0,1) with wrong 2";
  // Neg 4: (1,1)->3 wrong, scaled to (2,1)->4 wrong (correct 3)
  expect !IsMinCommands(2, 1, 4), "spec negative 4: (2,1) with wrong 4";
  // Neg 5: (1,1)->3 wrong, scaled to (1,0)->2 wrong (correct 1)
  expect !IsMinCommands(1, 0, 2), "spec negative 5: (1,0) with wrong 2";
  // Neg 6: (0,0)->1 wrong, scaled to (2,0)->4 wrong (correct 3)
  expect !IsMinCommands(2, 0, 4), "spec negative 6: (2,0) with wrong 4";

  // ===== IMPLEMENTATION TESTS =====
  // Test 1
  r := RobotProgram(5, 5);
  expect r == 10, "impl test 1-1: (5,5)";
  r := RobotProgram(3, 4);
  expect r == 7, "impl test 1-2: (3,4)";
  r := RobotProgram(7, 1);
  expect r == 13, "impl test 1-3: (7,1)";
  r := RobotProgram(0, 0);
  expect r == 0, "impl test 1-4: (0,0)";
  r := RobotProgram(2, 0);
  expect r == 3, "impl test 1-5: (2,0)";

  // Test 2: all (x,y) for 0<=x,y<=9
  r := RobotProgram(0, 0);
  expect r == 0, "impl test 2: (0,0)";
  r := RobotProgram(0, 1);
  expect r == 1, "impl test 2: (0,1)";
  r := RobotProgram(1, 0);
  expect r == 1, "impl test 2: (1,0)";
  r := RobotProgram(1, 1);
  expect r == 2, "impl test 2: (1,1)";
  r := RobotProgram(0, 2);
  expect r == 3, "impl test 2: (0,2)";
  r := RobotProgram(1, 2);
  expect r == 3, "impl test 2: (1,2)";
  r := RobotProgram(2, 0);
  expect r == 3, "impl test 2: (2,0)";
  r := RobotProgram(2, 1);
  expect r == 3, "impl test 2: (2,1)";
  r := RobotProgram(2, 2);
  expect r == 4, "impl test 2: (2,2)";
  r := RobotProgram(0, 3);
  expect r == 5, "impl test 2: (0,3)";
  r := RobotProgram(1, 3);
  expect r == 5, "impl test 2: (1,3)";
  r := RobotProgram(2, 3);
  expect r == 5, "impl test 2: (2,3)";
  r := RobotProgram(3, 0);
  expect r == 5, "impl test 2: (3,0)";
  r := RobotProgram(3, 1);
  expect r == 5, "impl test 2: (3,1)";
  r := RobotProgram(3, 2);
  expect r == 5, "impl test 2: (3,2)";
  r := RobotProgram(3, 3);
  expect r == 6, "impl test 2: (3,3)";
  r := RobotProgram(0, 4);
  expect r == 7, "impl test 2: (0,4)";
  r := RobotProgram(1, 4);
  expect r == 7, "impl test 2: (1,4)";
  r := RobotProgram(2, 4);
  expect r == 7, "impl test 2: (2,4)";
  r := RobotProgram(3, 4);
  expect r == 7, "impl test 2: (3,4)";
  r := RobotProgram(4, 0);
  expect r == 7, "impl test 2: (4,0)";
  r := RobotProgram(4, 1);
  expect r == 7, "impl test 2: (4,1)";
  r := RobotProgram(4, 2);
  expect r == 7, "impl test 2: (4,2)";
  r := RobotProgram(4, 3);
  expect r == 7, "impl test 2: (4,3)";
  r := RobotProgram(4, 4);
  expect r == 8, "impl test 2: (4,4)";
  r := RobotProgram(0, 5);
  expect r == 9, "impl test 2: (0,5)";
  r := RobotProgram(1, 5);
  expect r == 9, "impl test 2: (1,5)";
  r := RobotProgram(2, 5);
  expect r == 9, "impl test 2: (2,5)";
  r := RobotProgram(3, 5);
  expect r == 9, "impl test 2: (3,5)";
  r := RobotProgram(4, 5);
  expect r == 9, "impl test 2: (4,5)";
  r := RobotProgram(5, 0);
  expect r == 9, "impl test 2: (5,0)";
  r := RobotProgram(5, 1);
  expect r == 9, "impl test 2: (5,1)";
  r := RobotProgram(5, 2);
  expect r == 9, "impl test 2: (5,2)";
  r := RobotProgram(5, 3);
  expect r == 9, "impl test 2: (5,3)";
  r := RobotProgram(5, 4);
  expect r == 9, "impl test 2: (5,4)";
  r := RobotProgram(5, 5);
  expect r == 10, "impl test 2: (5,5)";
  r := RobotProgram(0, 6);
  expect r == 11, "impl test 2: (0,6)";
  r := RobotProgram(1, 6);
  expect r == 11, "impl test 2: (1,6)";
  r := RobotProgram(2, 6);
  expect r == 11, "impl test 2: (2,6)";
  r := RobotProgram(3, 6);
  expect r == 11, "impl test 2: (3,6)";
  r := RobotProgram(4, 6);
  expect r == 11, "impl test 2: (4,6)";
  r := RobotProgram(5, 6);
  expect r == 11, "impl test 2: (5,6)";
  r := RobotProgram(6, 0);
  expect r == 11, "impl test 2: (6,0)";
  r := RobotProgram(6, 1);
  expect r == 11, "impl test 2: (6,1)";
  r := RobotProgram(6, 2);
  expect r == 11, "impl test 2: (6,2)";
  r := RobotProgram(6, 3);
  expect r == 11, "impl test 2: (6,3)";
  r := RobotProgram(6, 4);
  expect r == 11, "impl test 2: (6,4)";
  r := RobotProgram(6, 5);
  expect r == 11, "impl test 2: (6,5)";
  r := RobotProgram(6, 6);
  expect r == 12, "impl test 2: (6,6)";
  r := RobotProgram(0, 7);
  expect r == 13, "impl test 2: (0,7)";
  r := RobotProgram(1, 7);
  expect r == 13, "impl test 2: (1,7)";
  r := RobotProgram(2, 7);
  expect r == 13, "impl test 2: (2,7)";
  r := RobotProgram(3, 7);
  expect r == 13, "impl test 2: (3,7)";
  r := RobotProgram(4, 7);
  expect r == 13, "impl test 2: (4,7)";
  r := RobotProgram(5, 7);
  expect r == 13, "impl test 2: (5,7)";
  r := RobotProgram(6, 7);
  expect r == 13, "impl test 2: (6,7)";
  r := RobotProgram(7, 0);
  expect r == 13, "impl test 2: (7,0)";
  r := RobotProgram(7, 1);
  expect r == 13, "impl test 2: (7,1)";
  r := RobotProgram(7, 2);
  expect r == 13, "impl test 2: (7,2)";
  r := RobotProgram(7, 3);
  expect r == 13, "impl test 2: (7,3)";
  r := RobotProgram(7, 4);
  expect r == 13, "impl test 2: (7,4)";
  r := RobotProgram(7, 5);
  expect r == 13, "impl test 2: (7,5)";
  r := RobotProgram(7, 6);
  expect r == 13, "impl test 2: (7,6)";
  r := RobotProgram(7, 7);
  expect r == 14, "impl test 2: (7,7)";
  r := RobotProgram(0, 8);
  expect r == 15, "impl test 2: (0,8)";
  r := RobotProgram(1, 8);
  expect r == 15, "impl test 2: (1,8)";
  r := RobotProgram(2, 8);
  expect r == 15, "impl test 2: (2,8)";
  r := RobotProgram(3, 8);
  expect r == 15, "impl test 2: (3,8)";
  r := RobotProgram(4, 8);
  expect r == 15, "impl test 2: (4,8)";
  r := RobotProgram(5, 8);
  expect r == 15, "impl test 2: (5,8)";
  r := RobotProgram(6, 8);
  expect r == 15, "impl test 2: (6,8)";
  r := RobotProgram(7, 8);
  expect r == 15, "impl test 2: (7,8)";
  r := RobotProgram(8, 0);
  expect r == 15, "impl test 2: (8,0)";
  r := RobotProgram(8, 1);
  expect r == 15, "impl test 2: (8,1)";
  r := RobotProgram(8, 2);
  expect r == 15, "impl test 2: (8,2)";
  r := RobotProgram(8, 3);
  expect r == 15, "impl test 2: (8,3)";
  r := RobotProgram(8, 4);
  expect r == 15, "impl test 2: (8,4)";
  r := RobotProgram(8, 5);
  expect r == 15, "impl test 2: (8,5)";
  r := RobotProgram(8, 6);
  expect r == 15, "impl test 2: (8,6)";
  r := RobotProgram(8, 7);
  expect r == 15, "impl test 2: (8,7)";
  r := RobotProgram(8, 8);
  expect r == 16, "impl test 2: (8,8)";
  r := RobotProgram(0, 9);
  expect r == 17, "impl test 2: (0,9)";
  r := RobotProgram(1, 9);
  expect r == 17, "impl test 2: (1,9)";
  r := RobotProgram(2, 9);
  expect r == 17, "impl test 2: (2,9)";
  r := RobotProgram(3, 9);
  expect r == 17, "impl test 2: (3,9)";
  r := RobotProgram(4, 9);
  expect r == 17, "impl test 2: (4,9)";
  r := RobotProgram(5, 9);
  expect r == 17, "impl test 2: (5,9)";
  r := RobotProgram(6, 9);
  expect r == 17, "impl test 2: (6,9)";
  r := RobotProgram(7, 9);
  expect r == 17, "impl test 2: (7,9)";
  r := RobotProgram(8, 9);
  expect r == 17, "impl test 2: (8,9)";
  r := RobotProgram(9, 0);
  expect r == 17, "impl test 2: (9,0)";
  r := RobotProgram(9, 1);
  expect r == 17, "impl test 2: (9,1)";
  r := RobotProgram(9, 2);
  expect r == 17, "impl test 2: (9,2)";
  r := RobotProgram(9, 3);
  expect r == 17, "impl test 2: (9,3)";
  r := RobotProgram(9, 4);
  expect r == 17, "impl test 2: (9,4)";
  r := RobotProgram(9, 5);
  expect r == 17, "impl test 2: (9,5)";
  r := RobotProgram(9, 6);
  expect r == 17, "impl test 2: (9,6)";
  r := RobotProgram(9, 7);
  expect r == 17, "impl test 2: (9,7)";
  r := RobotProgram(9, 8);
  expect r == 17, "impl test 2: (9,8)";
  r := RobotProgram(9, 9);
  expect r == 18, "impl test 2: (9,9)";

  // Test 3
  r := RobotProgram(999, 899);
  expect r == 1997, "impl test 3: (999,899)";

  // Test 4
  r := RobotProgram(1, 1);
  expect r == 2, "impl test 4: (1,1)";
  r := RobotProgram(5, 6);
  expect r == 11, "impl test 4: (5,6)";
  r := RobotProgram(7, 6);
  expect r == 13, "impl test 4: (7,6)";
  r := RobotProgram(3, 6);
  expect r == 11, "impl test 4: (3,6)";
  r := RobotProgram(8, 9);
  expect r == 17, "impl test 4: (8,9)";
  r := RobotProgram(9, 7);
  expect r == 17, "impl test 4: (9,7)";
  r := RobotProgram(5, 61);
  expect r == 121, "impl test 4: (5,61)";

  // Test 5
  r := RobotProgram(1, 1);
  expect r == 2, "impl test 5: (1,1)";
  r := RobotProgram(5, 6);
  expect r == 11, "impl test 5: (5,6)";
  r := RobotProgram(7, 6);
  expect r == 13, "impl test 5: (7,6)";
  r := RobotProgram(3, 6);
  expect r == 11, "impl test 5: (3,6)";
  r := RobotProgram(8, 9);
  expect r == 17, "impl test 5: (8,9)";
  r := RobotProgram(9, 7);
  expect r == 17, "impl test 5: (9,7)";
  r := RobotProgram(5, 6);
  expect r == 11, "impl test 5: (5,6) again";

  // Test 6
  r := RobotProgram(0, 0);
  expect r == 0, "impl test 6: (0,0) #1";
  r := RobotProgram(0, 0);
  expect r == 0, "impl test 6: (0,0) #2";
  r := RobotProgram(0, 0);
  expect r == 0, "impl test 6: (0,0) #3";
  r := RobotProgram(0, 0);
  expect r == 0, "impl test 6: (0,0) #4";
  r := RobotProgram(0, 0);
  expect r == 0, "impl test 6: (0,0) #5";
  r := RobotProgram(0, 0);
  expect r == 0, "impl test 6: (0,0) #6";
  r := RobotProgram(0, 0);
  expect r == 0, "impl test 6: (0,0) #7";

  print "All tests passed\n";
}
datatype Command = North | East | South | West | Stay

ghost function IntToCommand(i: int): Command
  requires 0 <= i <= 4
{
  if i == 0 then North
  else if i == 1 then East
  else if i == 2 then South
  else if i == 3 then West
  else Stay
}

ghost function DeltaX(cmd: Command): int {
  match cmd
  case North => 0
  case East => 1
  case South => 0
  case West => -1
  case Stay => 0
}

ghost function DeltaY(cmd: Command): int {
  match cmd
  case North => 1
  case East => 0
  case South => -1
  case West => 0
  case Stay => 0
}

// Can the robot reach (targetX, targetY) from (posX, posY) in exactly `steps` commands,
// given that `lastCmd` was the most recently executed command (-1 means no previous)?
// The robot cannot execute the same command twice in a row.
ghost predicate ReachableIn(posX: int, posY: int, targetX: int, targetY: int, steps: int, lastCmd: int)
  decreases if steps > 0 then steps else 0
{
  if steps < 0 then false
  else if steps == 0 then posX == targetX && posY == targetY
  else
    exists c | 0 <= c <= 4 :: c != lastCmd &&
      ReachableIn(posX + DeltaX(IntToCommand(c)), posY + DeltaY(IntToCommand(c)),
                  targetX, targetY, steps - 1, c)
}

// n is the minimum number of commands for the robot to reach (x, y) from (0, 0)
ghost predicate IsMinCommands(x: int, y: int, n: int) {
  n >= 0 &&
  ReachableIn(0, 0, x, y, n, -1) &&
  forall k :: 0 <= k < n ==> !ReachableIn(0, 0, x, y, k, -1)
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
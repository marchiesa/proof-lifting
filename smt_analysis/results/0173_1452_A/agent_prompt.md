Make this Dafny program verify. Add loop invariants, assertions, ghost variables,
and/or lemmas as needed. Do NOT modify the ghost spec (functions, predicates) or the method
signature (requires, ensures). Only add proof annotations inside method bodies.

## Problem: Robot Program
There is an infinite 2-dimensional grid. The robot stands in cell $$$(0, 0)$$$ and wants to reach cell $$$(x, y)$$$. Here is a list of possible commands the robot can execute:

- move north from cell $$$(i, j)$$$ to $$$(i, j + 1)$$$;
- move east from cell $$$(i, j)$$$ to $$$(i + 1, j)$$$;
- move south from cell $$$(i, j)$$$ to $$$(i, j - 1)$$$;
- move west from cell $$$(i, j)$$$ to $$$(i - 1, j)$$$;
- stay in cell $$$(i, j)$$$.

The robot wants to reach cell $$$(x, y)$$$ in as few commands as possible. However, he can't execute the same command two or more times in a row.

What is the minimum number of commands required to reach $$$(x, y)$$$ from $$$(0, 0)$$$?

## File: /Users/mchiesa/work/projects/2026-02-dafny-liftings/dataset/0173_1452_A/task.dfy

```dafny
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
```

## Instructions:

1. Read the code carefully. Understand what the method does and what the spec requires.

2. Add loop invariants for every loop. Common patterns:
   - Bounds: `invariant 0 <= i <= |s|`
   - Accumulator: `invariant acc == F(s[..i])` for recursive ghost functions
   - Sequence slicing: `assert s[..i+1] == s[..i] + [s[i]];` before using F(s[..i+1])
   - Full slice identity: `assert s[..|s|] == s;` after loops that process entire sequences
   - Type preservation: `invariant AllNonNeg(s[..i])` if needed by the spec

3. Add helper lemmas if needed (e.g., SumAppend, induction lemmas).

4. Run dafny verify:
   ```bash
   /opt/homebrew/Cellar/dotnet@8/8.0.124/libexec/dotnet /Users/mchiesa/work/projects/2026-02-dafny-liftings/dafny-source/Binaries/Dafny.dll verify /Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0173_1452_A/verified.dfy --verification-time-limit 60
   ```

5. If verification fails, read the error, fix the code, and retry.

6. Write the final result to `/Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0173_1452_A/verified.dfy`.
   Also write `/Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0173_1452_A/verify_result.json`:
   ```json
   {
     "verified": true/false,
     "attempts": N,
     "error": "last error if failed, null if verified"
   }
   ```

7. If you cannot verify after several attempts, save your best attempt as verified.dfy
   and set "verified": false in the result JSON.

IMPORTANT: Write output files to /Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0173_1452_A/ (create the directory if needed).

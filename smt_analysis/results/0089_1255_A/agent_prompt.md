Make this Dafny program verify. Add loop invariants, assertions, ghost variables,
and/or lemmas as needed. Do NOT modify the ghost spec (functions, predicates) or the method
signature (requires, ensures). Only add proof annotations inside method bodies.

## Problem: Changing Volume
Bob watches TV every day. He always sets the volume of his TV to $$$b$$$. However, today he is angry to find out someone has changed the volume to $$$a$$$. Of course, Bob has a remote control that can change the volume.

There are six buttons ($$$-5, -2, -1, +1, +2, +5$$$) on the control, which in one press can either increase or decrease the current volume by $$$1$$$, $$$2$$$, or $$$5$$$. The volume can be arbitrarily large, but can never be negative. In other words, Bob cannot press the button if it causes the volume to be lower than $$$0$$$.

As Bob is so angry, he wants to change the volume to $$$b$$$ using as few button presses as possible. However, he forgets how to do such simple calculations, so he asks you for help. Write a program that given $$$a$$$ and $$$b$$$, finds the minimum number of presses to change the TV volume from $$$a$$$ to $$$b$$$.

## File: /Users/mchiesa/work/projects/2026-02-dafny-liftings/dataset/0089_1255_A/task.dfy

```dafny
// The set of TV volumes reachable from `start` in at most `steps` button presses,
// where each press changes volume by one of {-5, -2, -1, +1, +2, +5}
// and the volume must remain non-negative after every press.
ghost function ReachableIn(start: int, steps: int): set<int>
  requires start >= 0
  requires steps >= 0
  decreases steps
{
  if steps == 0 then
    {start}
  else
    var prev := ReachableIn(start, steps - 1);
    prev + set v <- prev, d <- {-5, -2, -1, 1, 2, 5} | v + d >= 0 :: v + d
}

method ChangingVolume(a: int, b: int) returns (presses: int)
  requires a >= 0 && b >= 0
  ensures presses >= 0
  ensures b in ReachableIn(a, presses)
  ensures presses > 0 ==> b !in ReachableIn(a, presses - 1)
{
  var diff := if a > b then a - b else b - a;
  var fives := diff / 5;
  diff := diff % 5;
  var twos := diff / 2;
  diff := diff % 2;
  var ones := diff;
  presses := fives + twos + ones;
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
   /opt/homebrew/Cellar/dotnet@8/8.0.124/libexec/dotnet /Users/mchiesa/work/projects/2026-02-dafny-liftings/dafny-source/Binaries/Dafny.dll verify /Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0089_1255_A/verified.dfy --verification-time-limit 60
   ```

5. If verification fails, read the error, fix the code, and retry.

6. Write the final result to `/Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0089_1255_A/verified.dfy`.
   Also write `/Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0089_1255_A/verify_result.json`:
   ```json
   {
     "verified": true/false,
     "attempts": N,
     "error": "last error if failed, null if verified"
   }
   ```

7. If you cannot verify after several attempts, save your best attempt as verified.dfy
   and set "verified": false in the result JSON.

IMPORTANT: Write output files to /Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0089_1255_A/ (create the directory if needed).

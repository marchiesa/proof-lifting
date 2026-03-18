Make this Dafny program verify. Add loop invariants, assertions, ghost variables,
and/or lemmas as needed. Do NOT modify the ghost spec (functions, predicates) or the method
signature (requires, ensures). Only add proof annotations inside method bodies.

## Problem: Dice Rolling
Mishka got a six-faced dice. It has integer numbers from $$$2$$$ to $$$7$$$ written on its faces (all numbers on faces are different, so this is an almost usual dice).

Mishka wants to get exactly $$$x$$$ points by rolling his dice. The number of points is just a sum of numbers written at the topmost face of the dice for all the rolls Mishka makes.

Mishka doesn't really care about the number of rolls, so he just wants to know any number of rolls he can make to be able to get exactly $$$x$$$ points for them. Mishka is very lucky, so if the probability to get $$$x$$$ points with chosen number of rolls is non-zero, he will be able to roll the dice in such a way. Your task is to print this number. It is guaranteed that at least one answer exists.

Mishka is also very curious about different number of points to score so you have to answer $$$t$$$ independent queries.

## File: /Users/mchiesa/work/projects/2026-02-dafny-liftings/dataset/0029_1093_A/task.dfy

```dafny
// Sum of a sequence of integers
ghost function SumSeq(s: seq<int>): int
  decreases |s|
{
  if |s| == 0 then 0 else SumSeq(s[..|s|-1]) + s[|s|-1]
}

// A valid dice face: the six-faced die has faces {2, 3, 4, 5, 6, 7}
ghost predicate ValidDiceFace(v: int)
{
  2 <= v <= 7
}

// Every element in the sequence is a valid dice face
ghost predicate AllValidFaces(dice: seq<int>)
{
  forall i | 0 <= i < |dice| :: ValidDiceFace(dice[i])
}

// Construct a concrete dice sequence achieving a target sum.
// Each die starts at minimum face value 2; the extra (target - 2*numRolls) is
// distributed greedily, adding up to 5 to each die (since max face is 7 = 2+5).
ghost function BuildDiceWitness(extra: int, numLeft: int): seq<int>
  requires numLeft >= 0
  decreases numLeft
{
  if numLeft == 0 then []
  else if numLeft == 1 then [2 + extra]
  else
    var add := if extra > 5 then 5 else if extra < 0 then 0 else extra;
    [2 + add] + BuildDiceWitness(extra - add, numLeft - 1)
}

// Build a witness dice sequence for the given target and number of rolls
ghost function DiceWitness(target: int, numRolls: int): seq<int>
  requires numRolls >= 1
{
  BuildDiceWitness(target - 2 * numRolls, numRolls)
}

// numRolls is a correct answer for target iff there exists a sequence of
// numRolls dice faces (each in {2..7}) whose sum equals target.
ghost predicate IsCorrectAnswer(target: int, numRolls: int)
{
  numRolls >= 1 &&
  exists dice: seq<int> :: |dice| == numRolls &&
    AllValidFaces(dice) &&
    SumSeq(dice) == target
}

method DiceRolling(x: seq<int>) returns (rolls: seq<int>)
  requires forall i | 0 <= i < |x| :: x[i] >= 2
  ensures |rolls| == |x|
  ensures forall i | 0 <= i < |rolls| :: IsCorrectAnswer(x[i], rolls[i])
{
  rolls := [];
  var i := 0;
  while i < |x|
  {
    var val := x[i];
    if val <= 7 {
      rolls := rolls + [1];
    } else {
      var r := val / 7;
      if val % 7 != 0 {
        r := r + 1;
      }
      rolls := rolls + [r];
    }
    i := i + 1;
  }
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
   /opt/homebrew/Cellar/dotnet@8/8.0.124/libexec/dotnet /Users/mchiesa/work/projects/2026-02-dafny-liftings/dafny-source/Binaries/Dafny.dll verify /Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0029_1093_A/verified.dfy --verification-time-limit 60
   ```

5. If verification fails, read the error, fix the code, and retry.

6. Write the final result to `/Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0029_1093_A/verified.dfy`.
   Also write `/Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0029_1093_A/verify_result.json`:
   ```json
   {
     "verified": true/false,
     "attempts": N,
     "error": "last error if failed, null if verified"
   }
   ```

7. If you cannot verify after several attempts, save your best attempt as verified.dfy
   and set "verified": false in the result JSON.

IMPORTANT: Write output files to /Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0029_1093_A/ (create the directory if needed).

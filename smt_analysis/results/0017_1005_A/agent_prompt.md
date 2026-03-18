Make this Dafny program verify. Add loop invariants, assertions, ghost variables,
and/or lemmas as needed. Do NOT modify the ghost spec (functions, predicates) or the method
signature (requires, ensures). Only add proof annotations inside method bodies.

## Problem: Tanya and Stairways
Little girl Tanya climbs the stairs inside a multi-storey building. Every time Tanya climbs a stairway, she starts counting steps from $$$1$$$ to the number of steps in this stairway. She speaks every number aloud. For example, if she climbs two stairways, the first of which contains $$$3$$$ steps, and the second contains $$$4$$$ steps, she will pronounce the numbers $$$1, 2, 3, 1, 2, 3, 4$$$.

You are given all the numbers pronounced by Tanya. How many stairways did she climb? Also, output the number of steps in each stairway.

The given sequence will be a valid sequence that Tanya could have pronounced when climbing one or more stairways.

## File: /Users/mchiesa/work/projects/2026-02-dafny-liftings/dataset/0017_1005_A/task.dfy

```dafny
// Generates the counting sequence [1, 2, ..., n]
ghost function CountingSeq(n: int): seq<int>
  decreases n
{
  if n <= 0 then [] else CountingSeq(n - 1) + [n]
}

// Every element is at least 1 (each stairway has at least one step)
ghost predicate AllPositive(s: seq<int>)
{
  forall i | 0 <= i < |s| :: s[i] >= 1
}

// Concatenates counting sequences: [1..stairs[0]] ++ [1..stairs[1]] ++ ...
ghost function ConcatStairways(stairs: seq<int>): seq<int>
  decreases |stairs|
{
  if |stairs| == 0 then []
  else ConcatStairways(stairs[..|stairs|-1]) + CountingSeq(stairs[|stairs|-1])
}

// The input is a valid pronunciation: starts at 1, each next element
// either starts a new stairway (== 1) or continues the count (== prev + 1)
ghost predicate IsValidInput(a: seq<int>)
{
  |a| >= 1 &&
  a[0] == 1 &&
  forall i | 1 <= i < |a| :: a[i] == 1 || a[i] == a[i - 1] + 1
}

method TanyaAndStairways(a: seq<int>) returns (t: int, stairs: seq<int>)
  requires IsValidInput(a)
  ensures t == |stairs|
  ensures t >= 1
  ensures AllPositive(stairs)
  ensures ConcatStairways(stairs) == a
{
  stairs := [];
  var cnt := 0;
  for i := 0 to |a| {
    if i == 0 {
      cnt := 1;
    } else if a[i] == 1 {
      stairs := stairs + [cnt];
      cnt := 1;
    } else {
      cnt := cnt + 1;
    }
  }
  stairs := stairs + [cnt];
  t := |stairs|;
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
   /opt/homebrew/Cellar/dotnet@8/8.0.124/libexec/dotnet /Users/mchiesa/work/projects/2026-02-dafny-liftings/dafny-source/Binaries/Dafny.dll verify /Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0017_1005_A/verified.dfy --verification-time-limit 60
   ```

5. If verification fails, read the error, fix the code, and retry.

6. Write the final result to `/Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0017_1005_A/verified.dfy`.
   Also write `/Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0017_1005_A/verify_result.json`:
   ```json
   {
     "verified": true/false,
     "attempts": N,
     "error": "last error if failed, null if verified"
   }
   ```

7. If you cannot verify after several attempts, save your best attempt as verified.dfy
   and set "verified": false in the result JSON.

IMPORTANT: Write output files to /Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0017_1005_A/ (create the directory if needed).

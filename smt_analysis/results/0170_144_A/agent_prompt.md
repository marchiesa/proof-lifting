Make this Dafny program verify. Add loop invariants, assertions, ghost variables,
and/or lemmas as needed. Do NOT modify the ghost spec (functions, predicates) or the method
signature (requires, ensures). Only add proof annotations inside method bodies.

## Problem: Arrival of the General
A Ministry for Defense sent a general to inspect the Super Secret Military Squad under the command of the Colonel SuperDuper. Having learned the news, the colonel ordered to all n squad soldiers to line up on the parade ground.

By the military charter the soldiers should stand in the order of non-increasing of their height. But as there's virtually no time to do that, the soldiers lined up in the arbitrary order. However, the general is rather short-sighted and he thinks that the soldiers lined up correctly if the first soldier in the line has the maximum height and the last soldier has the minimum height. Please note that the way other solders are positioned does not matter, including the case when there are several soldiers whose height is maximum or minimum. Only the heights of the first and the last soldier are important.

For example, the general considers the sequence of heights (4, 3, 4, 2, 1, 1) correct and the sequence (4, 3, 1, 2, 2) wrong.

Within one second the colonel can swap any two neighboring soldiers. Help him count the minimum time needed to form a line-up which the general will consider correct.

## File: /Users/mchiesa/work/projects/2026-02-dafny-liftings/dataset/0170_144_A/task.dfy

```dafny
ghost function SeqMax(s: seq<int>): int
  requires |s| > 0
  decreases |s|
{
  if |s| == 1 then s[0]
  else
    var m := SeqMax(s[..|s| - 1]);
    if s[|s| - 1] > m then s[|s| - 1] else m
}

ghost function SeqMin(s: seq<int>): int
  requires |s| > 0
  decreases |s|
{
  if |s| == 1 then s[0]
  else
    var m := SeqMin(s[..|s| - 1]);
    if s[|s| - 1] < m then s[|s| - 1] else m
}

// One adjacent swap: exchange elements at positions i and i+1
ghost function SwapAdj(s: seq<int>, i: int): seq<int>
  requires 0 <= i < |s| - 1
  ensures |SwapAdj(s, i)| == |s|
{
  s[i := s[i + 1]][i + 1 := s[i]]
}

// The general approves a lineup if the first soldier is tallest and the last is shortest
ghost predicate GeneralApproves(lineup: seq<int>, original: seq<int>)
  requires |lineup| > 0 && |original| > 0 && |lineup| == |original|
{
  lineup[0] == SeqMax(original) && lineup[|lineup| - 1] == SeqMin(original)
}

// Can we reach a general-approved configuration from s using at most `budget` adjacent swaps?
ghost predicate CanReachApproved(s: seq<int>, original: seq<int>, budget: int)
  requires |s| > 0 && |original| > 0 && |s| == |original|
  requires budget >= 0
  decreases budget
{
  GeneralApproves(s, original)
  ||
  (budget > 0 &&
   exists i | 0 <= i < |s| - 1 :: CanReachApproved(SwapAdj(s, i), original, budget - 1))
}

method ArrivalOfTheGeneral(a: seq<int>) returns (swaps: int)
  ensures |a| == 0 ==> swaps == 0
  ensures |a| > 0 ==> swaps >= 0 && CanReachApproved(a, a, swaps)
  ensures |a| > 0 ==> forall k | 0 <= k < swaps :: !CanReachApproved(a, a, k)
{
  var n := |a|;
  if n == 0 {
    return 0;
  }

  var mn := a[0];
  var mx := a[0];
  var i := 1;
  while i < n {
    if a[i] < mn { mn := a[i]; }
    if a[i] > mx { mx := a[i]; }
    i := i + 1;
  }

  var res := n * n;

  // Strategy 1: move max to front first, then min to end
  var cur := 0;
  var na := new int[n];
  i := 0;
  while i < n {
    na[i] := a[i];
    i := i + 1;
  }

  var pmx := -1;
  i := 0;
  while i < n {
    if na[i] == mx { pmx := i; break; }
    i := i + 1;
  }

  i := pmx - 1;
  while i >= 0 {
    var tmp := na[i]; na[i] := na[i + 1]; na[i + 1] := tmp;
    cur := cur + 1;
    i := i - 1;
  }

  var pmn := -1;
  i := n - 1;
  while i >= 0 {
    if na[i] == mn { pmn := i; break; }
    i := i - 1;
  }

  i := pmn;
  while i < n - 1 {
    var tmp := na[i]; na[i] := na[i + 1]; na[i + 1] := tmp;
    cur := cur + 1;
    i := i + 1;
  }

  if cur < res { res := cur; }

  // Strategy 2: move min to end first, then max to front
  cur := 0;
  i := 0;
  while i < n {
    na[i] := a[i];
    i := i + 1;
  }

  pmn := -1;
  i := n - 1;
  while i >= 0 {
    if na[i] == mn { pmn := i; break; }
    i := i - 1;
  }

  i := pmn;
  while i < n - 1 {
    var tmp := na[i]; na[i] := na[i + 1]; na[i + 1] := tmp;
    cur := cur + 1;
    i := i + 1;
  }

  pmx := -1;
  i := 0;
  while i < n {
    if na[i] == mx { pmx := i; break; }
    i := i + 1;
  }

  i := pmx - 1;
  while i >= 0 {
    var tmp := na[i]; na[i] := na[i + 1]; na[i + 1] := tmp;
    cur := cur + 1;
    i := i - 1;
  }

  if cur < res { res := cur; }

  swaps := res;
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
   /opt/homebrew/Cellar/dotnet@8/8.0.124/libexec/dotnet /Users/mchiesa/work/projects/2026-02-dafny-liftings/dafny-source/Binaries/Dafny.dll verify /Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0170_144_A/verified.dfy --verification-time-limit 60
   ```

5. If verification fails, read the error, fix the code, and retry.

6. Write the final result to `/Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0170_144_A/verified.dfy`.
   Also write `/Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0170_144_A/verify_result.json`:
   ```json
   {
     "verified": true/false,
     "attempts": N,
     "error": "last error if failed, null if verified"
   }
   ```

7. If you cannot verify after several attempts, save your best attempt as verified.dfy
   and set "verified": false in the result JSON.

IMPORTANT: Write output files to /Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0170_144_A/ (create the directory if needed).

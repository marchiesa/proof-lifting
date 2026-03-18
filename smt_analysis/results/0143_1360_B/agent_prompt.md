Make this Dafny program verify. Add loop invariants, assertions, ghost variables,
and/or lemmas as needed. Do NOT modify the ghost spec (functions, predicates) or the method
signature (requires, ensures). Only add proof annotations inside method bodies.

## Problem: Honest Coach
There are $$$n$$$ athletes in front of you. Athletes are numbered from $$$1$$$ to $$$n$$$ from left to right. You know the strength of each athlete — the athlete number $$$i$$$ has the strength $$$s_i$$$.

You want to split all athletes into two teams. Each team must have at least one athlete, and each athlete must be exactly in one team.

You want the strongest athlete from the first team to differ as little as possible from the weakest athlete from the second team. Formally, you want to split the athletes into two teams $$$A$$$ and $$$B$$$ so that the value $$$|\max(A) - \min(B)|$$$ is as small as possible, where $$$\max(A)$$$ is the maximum strength of an athlete from team $$$A$$$, and $$$\min(B)$$$ is the minimum strength of an athlete from team $$$B$$$.

For example, if $$$n=5$$$ and the strength of the athletes is $$$s=[3, 1, 2, 6, 4]$$$, then one of the possible split into teams is:

- first team: $$$A = [1, 2, 4]$$$,
- second team: $$$B = [3, 6]$$$.

In this case, the value $$$|\max(A) - \min(B)|$$$ will be equal to $$$|4-3|=1$$$. This example illustrates one of the ways of optimal split into two teams.

Print the minimum value $$$|\max(A) - \min(B)|$$$.

## File: /Users/mchiesa/work/projects/2026-02-dafny-liftings/dataset/0143_1360_B/task.dfy

```dafny
// --- Specification: model the problem's partition structure ---

ghost function Pow2(n: nat): nat
  decreases n
{
  if n == 0 then 1 else 2 * Pow2(n - 1)
}

ghost predicate BitSet(mask: nat, i: nat)
{
  (mask / Pow2(i)) % 2 == 1
}

// Extract the sub-sequence of athletes assigned to team A (selectA=true) or team B (selectA=false)
ghost function FilterTeam(s: seq<int>, mask: nat, selectA: bool): seq<int>
  decreases |s|
{
  if |s| == 0 then []
  else
    var rest := FilterTeam(s[..|s|-1], mask, selectA);
    if BitSet(mask, |s| - 1) == selectA then rest + [s[|s|-1]]
    else rest
}

ghost function SeqMax(a: seq<int>): int
  requires |a| >= 1
  decreases |a|
{
  if |a| == 1 then a[0]
  else
    var rest := SeqMax(a[..|a|-1]);
    if a[|a|-1] > rest then a[|a|-1] else rest
}

ghost function SeqMin(a: seq<int>): int
  requires |a| >= 1
  decreases |a|
{
  if |a| == 1 then a[0]
  else
    var rest := SeqMin(a[..|a|-1]);
    if a[|a|-1] < rest then a[|a|-1] else rest
}

ghost function Abs(x: int): int
{
  if x >= 0 then x else -x
}

// Cost of splitting s according to bitmask: |max(teamA) - min(teamB)|
// Returns -1 for degenerate splits (one team empty); valid masks never hit this case.
ghost function SplitCost(s: seq<int>, mask: nat): int
{
  var teamA := FilterTeam(s, mask, true);
  var teamB := FilterTeam(s, mask, false);
  if |teamA| >= 1 && |teamB| >= 1 then
    Abs(SeqMax(teamA) - SeqMin(teamB))
  else
    -1
}

// --- Method with formal specification ---
// A bitmask in [1, 2^n - 2] encodes every partition of n athletes into two non-empty teams:
//   bit i set  => athlete i in team A
//   bit i clear => athlete i in team B
// The result is the minimum |max(A) - min(B)| over all such partitions.

method HonestCoach(s: seq<int>) returns (minDiff: int)
  requires |s| >= 2
  ensures forall mask :: 1 <= mask <= Pow2(|s|) - 2 ==> SplitCost(s, mask) >= minDiff
  ensures exists mask | 1 <= mask <= Pow2(|s|) - 2 :: SplitCost(s, mask) == minDiff
{
  var a := s;
  // Sort (insertion sort)
  var i := 1;
  while i < |a|
  {
    var j := i;
    while j > 0 && a[j-1] > a[j]
    {
      var tmp := a[j-1];
      a := a[j-1 := a[j]][j := tmp];
      j := j - 1;
    }
    i := i + 1;
  }
  // Find minimum consecutive difference
  minDiff := a[1] - a[0];
  i := 2;
  while i < |a|
  {
    var diff := a[i] - a[i-1];
    if diff < minDiff {
      minDiff := diff;
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
   /opt/homebrew/Cellar/dotnet@8/8.0.124/libexec/dotnet /Users/mchiesa/work/projects/2026-02-dafny-liftings/dafny-source/Binaries/Dafny.dll verify /Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0143_1360_B/verified.dfy --verification-time-limit 60
   ```

5. If verification fails, read the error, fix the code, and retry.

6. Write the final result to `/Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0143_1360_B/verified.dfy`.
   Also write `/Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0143_1360_B/verify_result.json`:
   ```json
   {
     "verified": true/false,
     "attempts": N,
     "error": "last error if failed, null if verified"
   }
   ```

7. If you cannot verify after several attempts, save your best attempt as verified.dfy
   and set "verified": false in the result JSON.

IMPORTANT: Write output files to /Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0143_1360_B/ (create the directory if needed).

Make this Dafny program verify. Add loop invariants, assertions, ghost variables,
and/or lemmas as needed. Do NOT modify the ghost spec (functions, predicates) or the method
signature (requires, ensures). Only add proof annotations inside method bodies.

## Problem: Yet Another Dividing into Teams
You are a coach of a group consisting of $$$n$$$ students. The $$$i$$$-th student has programming skill $$$a_i$$$. All students have distinct programming skills. You want to divide them into teams in such a way that:

- No two students $$$i$$$ and $$$j$$$ such that $$$|a_i - a_j| = 1$$$ belong to the same team (i.e. skills of each pair of students in the same team have the difference strictly greater than $$$1$$$);
- the number of teams is the minimum possible.

You have to answer $$$q$$$ independent queries.

## File: /Users/mchiesa/work/projects/2026-02-dafny-liftings/dataset/0088_1249_A/task.dfy

```dafny
ghost function Abs(x: int): int
{
  if x >= 0 then x else -x
}

// True when some pair of elements in a differ by exactly 1
ghost predicate HasAdjacentPair(a: seq<int>)
{
  exists i, j | 0 <= i < |a| && 0 <= j < |a| && i != j :: Abs(a[i] - a[j]) == 1
}

// A valid team assignment: each student maps to a team in [0..numTeams),
// and no two students on the same team have skill values differing by 1.
ghost predicate ValidAssignment(a: seq<int>, assignment: seq<int>, numTeams: int)
{
  |assignment| == |a| &&
  numTeams >= 1 &&
  (forall i | 0 <= i < |a| :: 0 <= assignment[i] < numTeams) &&
  (forall i, j | 0 <= i < |a| && 0 <= j < |a| && i != j ::
    assignment[i] == assignment[j] ==> Abs(a[i] - a[j]) != 1)
}

// Constant sequence of length |a| — witness that 1 team suffices when no adjacent pair exists
ghost function ConstantSeq(a: seq<int>, v: int): seq<int>
  decreases |a|
{
  if |a| == 0 then []
  else ConstantSeq(a[..|a|-1], v) + [v]
}

// Parity-based assignment: team = a[i] % 2.
// If |a[i] - a[j]| = 1 then a[i] and a[j] have different parities,
// so they land on different teams. This witnesses 2-colorability.
ghost function ParityAssignment(a: seq<int>): seq<int>
  decreases |a|
{
  if |a| == 0 then []
  else ParityAssignment(a[..|a|-1]) + [a[|a|-1] % 2]
}

method YetAnotherDividingIntoTeams(a: seq<int>) returns (teams: int)
  // All programming skills are distinct and in [1, 100]
  requires forall i, j | 0 <= i < |a| && 0 <= j < |a| && i != j :: a[i] != a[j]
  requires forall i | 0 <= i < |a| :: 1 <= a[i] <= 100
  ensures teams == 1 || teams == 2
  // Feasibility: a valid partition into `teams` teams exists (constructive witness)
  ensures ValidAssignment(a, if teams == 1 then ConstantSeq(a, 0) else ParityAssignment(a), teams)
  // Minimality: 2 teams are needed iff there is a pair of students with adjacent skills
  ensures HasAdjacentPair(a) <==> teams == 2
{
  var b := new int[102];
  var i := 0;
  while i < 102 {
    b[i] := 0;
    i := i + 1;
  }
  i := 0;
  while i < |a| {
    if 0 <= a[i] < 102 {
      b[a[i]] := b[a[i]] + 1;
    }
    i := i + 1;
  }
  var flag := false;
  i := 1;
  while i <= 100 {
    if b[i] == 1 && (b[i + 1] == 1 || b[i - 1] == 1) {
      flag := true;
    }
    i := i + 1;
  }
  if flag {
    teams := 2;
  } else {
    teams := 1;
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
   /opt/homebrew/Cellar/dotnet@8/8.0.124/libexec/dotnet /Users/mchiesa/work/projects/2026-02-dafny-liftings/dafny-source/Binaries/Dafny.dll verify /Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0088_1249_A/verified.dfy --verification-time-limit 60
   ```

5. If verification fails, read the error, fix the code, and retry.

6. Write the final result to `/Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0088_1249_A/verified.dfy`.
   Also write `/Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0088_1249_A/verify_result.json`:
   ```json
   {
     "verified": true/false,
     "attempts": N,
     "error": "last error if failed, null if verified"
   }
   ```

7. If you cannot verify after several attempts, save your best attempt as verified.dfy
   and set "verified": false in the result JSON.

IMPORTANT: Write output files to /Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0088_1249_A/ (create the directory if needed).

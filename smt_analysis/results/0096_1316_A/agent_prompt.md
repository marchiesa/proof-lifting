Make this Dafny program verify. Add loop invariants, assertions, ghost variables,
and/or lemmas as needed. Do NOT modify the ghost spec (functions, predicates) or the method
signature (requires, ensures). Only add proof annotations inside method bodies.

## Problem: Grade Allocation
$$$n$$$ students are taking an exam. The highest possible score at this exam is $$$m$$$. Let $$$a_{i}$$$ be the score of the $$$i$$$-th student. You have access to the school database which stores the results of all students.

You can change each student's score as long as the following conditions are satisfied:

- All scores are integers
- $$$0 \leq a_{i} \leq m$$$
- The average score of the class doesn't change.

You are student $$$1$$$ and you would like to maximize your own score.

Find the highest possible score you can assign to yourself such that all conditions are satisfied.

## File: /Users/mchiesa/work/projects/2026-02-dafny-liftings/dataset/0096_1316_A/task.dfy

```dafny
ghost function Sum(a: seq<int>): int
  decreases |a|
{
  if |a| == 0 then 0 else Sum(a[..|a|-1]) + a[|a|-1]
}

ghost predicate ValidScores(a: seq<int>, m: int)
{
  forall i | 0 <= i < |a| :: 0 <= a[i] <= m
}

// A score v is achievable for student 0 if there exists a reassignment
// b[0..n-1] with b[0] = v, all b[i] in [0, m], and Sum(b) == Sum(a).
// This holds iff v is in [0, m] and the remaining sum Sum(a) - v can be
// distributed among |a| - 1 students each scoring in [0, m].
ghost predicate Achievable(a: seq<int>, m: int, v: int)
  requires |a| > 0
{
  0 <= v <= m &&
  Sum(a) - v >= 0 &&
  Sum(a) - v <= (|a| - 1) * m
}

method GradeAllocation(a: seq<int>, m: int) returns (score: int)
  requires |a| > 0
  requires m >= 0
  requires ValidScores(a, m)
  ensures Achievable(a, m, score)
  ensures forall v | score < v <= m :: !Achievable(a, m, v)
{
  var s := 0;
  var i := 0;
  while i < |a|
  {
    s := s + a[i];
    i := i + 1;
  }
  if s < m {
    score := s;
  } else {
    score := m;
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
   /opt/homebrew/Cellar/dotnet@8/8.0.124/libexec/dotnet /Users/mchiesa/work/projects/2026-02-dafny-liftings/dafny-source/Binaries/Dafny.dll verify /Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0096_1316_A/verified.dfy --verification-time-limit 60
   ```

5. If verification fails, read the error, fix the code, and retry.

6. Write the final result to `/Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0096_1316_A/verified.dfy`.
   Also write `/Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0096_1316_A/verify_result.json`:
   ```json
   {
     "verified": true/false,
     "attempts": N,
     "error": "last error if failed, null if verified"
   }
   ```

7. If you cannot verify after several attempts, save your best attempt as verified.dfy
   and set "verified": false in the result JSON.

IMPORTANT: Write output files to /Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0096_1316_A/ (create the directory if needed).

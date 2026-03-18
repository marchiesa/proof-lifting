Make this Dafny program verify. Add loop invariants, assertions, ghost variables,
and/or lemmas as needed. Do NOT modify the ghost spec (functions, predicates) or the method
signature (requires, ensures). Only add proof annotations inside method bodies.

## Problem: In Search of an Easy Problem
When preparing a tournament, Codeforces coordinators try treir best to make the first problem as easy as possible. This time the coordinator had chosen some problem and asked $$$n$$$ people about their opinions. Each person answered whether this problem is easy or hard.

If at least one of these $$$n$$$ people has answered that the problem is hard, the coordinator decides to change the problem. For the given responses, check if the problem is easy enough.

## File: /Users/mchiesa/work/projects/2026-02-dafny-liftings/dataset/0011_1030_A/task.dfy

```dafny
ghost predicate AllConsiderEasy(opinions: seq<int>)
{
  forall i | 0 <= i < |opinions| :: opinions[i] == 0
}

method IsEasyProblem(n: int, opinions: seq<int>) returns (result: string)
  ensures AllConsiderEasy(opinions) ==> result == "EASY"
  ensures !AllConsiderEasy(opinions) ==> result == "HARD"
{
  var allZero := true;
  var i := 0;
  while i < |opinions|
  {
    if opinions[i] != 0 {
      allZero := false;
    }
    i := i + 1;
  }
  if allZero {
    result := "EASY";
  } else {
    result := "HARD";
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
   /opt/homebrew/Cellar/dotnet@8/8.0.124/libexec/dotnet /Users/mchiesa/work/projects/2026-02-dafny-liftings/dafny-source/Binaries/Dafny.dll verify /Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0011_1030_A/verified.dfy --verification-time-limit 60
   ```

5. If verification fails, read the error, fix the code, and retry.

6. Write the final result to `/Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0011_1030_A/verified.dfy`.
   Also write `/Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0011_1030_A/verify_result.json`:
   ```json
   {
     "verified": true/false,
     "attempts": N,
     "error": "last error if failed, null if verified"
   }
   ```

7. If you cannot verify after several attempts, save your best attempt as verified.dfy
   and set "verified": false in the result JSON.

IMPORTANT: Write output files to /Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0011_1030_A/ (create the directory if needed).

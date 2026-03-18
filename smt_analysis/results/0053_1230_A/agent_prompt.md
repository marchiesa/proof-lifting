Make this Dafny program verify. Add loop invariants, assertions, ghost variables,
and/or lemmas as needed. Do NOT modify the ghost spec (functions, predicates) or the method
signature (requires, ensures). Only add proof annotations inside method bodies.

## Problem: Dawid and Bags of Candies
Dawid has four bags of candies. The $$$i$$$-th of them contains $$$a_i$$$ candies. Also, Dawid has two friends. He wants to give each bag to one of his two friends. Is it possible to distribute the bags in such a way that each friend receives the same amount of candies in total?

Note, that you can't keep bags for yourself or throw them away, each bag should be given to one of the friends.

## File: /Users/mchiesa/work/projects/2026-02-dafny-liftings/dataset/0053_1230_A/task.dfy

```dafny
ghost function FriendSum(a1: int, a2: int, a3: int, a4: int,
                   b1: bool, b2: bool, b3: bool, b4: bool): int
{
  (if b1 then a1 else 0) + (if b2 then a2 else 0) +
  (if b3 then a3 else 0) + (if b4 then a4 else 0)
}

ghost predicate CanDistributeEqually(a1: int, a2: int, a3: int, a4: int)
{
  exists b1: bool, b2: bool, b3: bool, b4: bool ::
    FriendSum(a1, a2, a3, a4, b1, b2, b3, b4) ==
    FriendSum(a1, a2, a3, a4, !b1, !b2, !b3, !b4)
}

method DawidAndCandies(a1: int, a2: int, a3: int, a4: int) returns (result: bool)
  requires a1 >= 1 && a2 >= 1 && a3 >= 1 && a4 >= 1
  ensures result == CanDistributeEqually(a1, a2, a3, a4)
{
  result := (a1 + a2 == a3 + a4) || (a1 + a3 == a2 + a4) || (a1 + a4 == a2 + a3) ||
            (a1 + a2 + a3 == a4) || (a1 + a2 + a4 == a3) || (a1 + a3 + a4 == a2) || (a2 + a3 + a4 == a1);
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
   /opt/homebrew/Cellar/dotnet@8/8.0.124/libexec/dotnet /Users/mchiesa/work/projects/2026-02-dafny-liftings/dafny-source/Binaries/Dafny.dll verify /Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0053_1230_A/verified.dfy --verification-time-limit 60
   ```

5. If verification fails, read the error, fix the code, and retry.

6. Write the final result to `/Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0053_1230_A/verified.dfy`.
   Also write `/Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0053_1230_A/verify_result.json`:
   ```json
   {
     "verified": true/false,
     "attempts": N,
     "error": "last error if failed, null if verified"
   }
   ```

7. If you cannot verify after several attempts, save your best attempt as verified.dfy
   and set "verified": false in the result JSON.

IMPORTANT: Write output files to /Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0053_1230_A/ (create the directory if needed).

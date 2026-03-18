Make this Dafny program verify. Add loop invariants, assertions, ghost variables,
and/or lemmas as needed. Do NOT modify the ghost spec (functions, predicates) or the method
signature (requires, ensures). Only add proof annotations inside method bodies.

## Problem: Candies and Two Sisters
There are two sisters Alice and Betty. You have $$$n$$$ candies. You want to distribute these $$$n$$$ candies between two sisters in such a way that:

- Alice will get $$$a$$$ ($$$a > 0$$$) candies;
- Betty will get $$$b$$$ ($$$b > 0$$$) candies;
- each sister will get some integer number of candies;
- Alice will get a greater amount of candies than Betty (i.e. $$$a > b$$$);
- all the candies will be given to one of two sisters (i.e. $$$a+b=n$$$).

Your task is to calculate the number of ways to distribute exactly $$$n$$$ candies between sisters in a way described above. Candies are indistinguishable.

Formally, find the number of ways to represent $$$n$$$ as the sum of $$$n=a+b$$$, where $$$a$$$ and $$$b$$$ are positive integers and $$$a>b$$$.

You have to answer $$$t$$$ independent test cases.

## File: /Users/mchiesa/work/projects/2026-02-dafny-liftings/dataset/0145_1335_A/task.dfy

```dafny
ghost predicate ValidDistribution(n: int, a: int, b: int) {
  a > 0 && b > 0 && a > b && a + b == n
}

ghost function CountDistributions(n: int, hi: int): int
  requires hi >= 0
  decreases hi
{
  if hi < 1 then 0
  else CountDistributions(n, hi - 1) + (if ValidDistribution(n, n - hi, hi) then 1 else 0)
}

method Candies(n: int) returns (ways: int)
  requires n >= 1
  ensures ways == CountDistributions(n, n - 1)
{
  if n <= 2 {
    ways := 0;
  } else {
    ways := (n - 1) / 2;
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
   /opt/homebrew/Cellar/dotnet@8/8.0.124/libexec/dotnet /Users/mchiesa/work/projects/2026-02-dafny-liftings/dafny-source/Binaries/Dafny.dll verify /Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0145_1335_A/verified.dfy --verification-time-limit 60
   ```

5. If verification fails, read the error, fix the code, and retry.

6. Write the final result to `/Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0145_1335_A/verified.dfy`.
   Also write `/Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0145_1335_A/verify_result.json`:
   ```json
   {
     "verified": true/false,
     "attempts": N,
     "error": "last error if failed, null if verified"
   }
   ```

7. If you cannot verify after several attempts, save your best attempt as verified.dfy
   and set "verified": false in the result JSON.

IMPORTANT: Write output files to /Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0145_1335_A/ (create the directory if needed).

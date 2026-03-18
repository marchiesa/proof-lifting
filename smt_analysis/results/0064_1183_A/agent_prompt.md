Make this Dafny program verify. Add loop invariants, assertions, ghost variables,
and/or lemmas as needed. Do NOT modify the ghost spec (functions, predicates) or the method
signature (requires, ensures). Only add proof annotations inside method bodies.

## Problem: Nearest Interesting Number
Polycarp knows that if the sum of the digits of a number is divisible by $$$3$$$, then the number itself is divisible by $$$3$$$. He assumes that the numbers, the sum of the digits of which is divisible by $$$4$$$, are also somewhat interesting. Thus, he considers a positive integer $$$n$$$ interesting if its sum of digits is divisible by $$$4$$$.

Help Polycarp find the nearest larger or equal interesting number for the given number $$$a$$$. That is, find the interesting number $$$n$$$ such that $$$n \ge a$$$ and $$$n$$$ is minimal.

## File: /Users/mchiesa/work/projects/2026-02-dafny-liftings/dataset/0064_1183_A/task.dfy

```dafny
ghost function DigitSum(n: int): int
  requires n >= 0
  decreases n
{
  if n == 0 then 0
  else n % 10 + DigitSum(n / 10)
}

ghost predicate IsInteresting(n: int)
  requires n >= 0
{
  DigitSum(n) == 18
}

method SumDigits(x: int) returns (s: int)
  requires x >= 0
  ensures s == DigitSum(x)
  decreases *
{
  s := 0;
  var tmp := x;
  while tmp > 0
    decreases *
  {
    s := s + tmp % 10;
    tmp := tmp / 10;
  }
}

method NearestInterestingNumber(a: int) returns (n: int)
  requires a >= 1
  ensures n >= a
  ensures IsInteresting(n)
  ensures forall k :: a <= k < n ==> !IsInteresting(k)
  decreases *
{
  n := a;
  var s := SumDigits(n);
  while s != 18
    decreases *
  {
    n := n + 1;
    s := SumDigits(n);
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
   /opt/homebrew/Cellar/dotnet@8/8.0.124/libexec/dotnet /Users/mchiesa/work/projects/2026-02-dafny-liftings/dafny-source/Binaries/Dafny.dll verify /Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0064_1183_A/verified.dfy --verification-time-limit 60
   ```

5. If verification fails, read the error, fix the code, and retry.

6. Write the final result to `/Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0064_1183_A/verified.dfy`.
   Also write `/Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0064_1183_A/verify_result.json`:
   ```json
   {
     "verified": true/false,
     "attempts": N,
     "error": "last error if failed, null if verified"
   }
   ```

7. If you cannot verify after several attempts, save your best attempt as verified.dfy
   and set "verified": false in the result JSON.

IMPORTANT: Write output files to /Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0064_1183_A/ (create the directory if needed).

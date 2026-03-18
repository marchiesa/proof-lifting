Make this Dafny program verify. Add loop invariants, assertions, ghost variables,
and/or lemmas as needed. Do NOT modify the ghost spec (functions, predicates) or the method
signature (requires, ensures). Only add proof annotations inside method bodies.

## Problem: Maximum GCD
Let's consider all integers in the range from $$$1$$$ to $$$n$$$ (inclusive).

Among all pairs of distinct integers in this range, find the maximum possible greatest common divisor of integers in pair. Formally, find the maximum value of $$$\mathrm{gcd}(a, b)$$$, where $$$1 \leq a < b \leq n$$$.

The greatest common divisor, $$$\mathrm{gcd}(a, b)$$$, of two positive integers $$$a$$$ and $$$b$$$ is the biggest integer that is a divisor of both $$$a$$$ and $$$b$$$.

## File: /Users/mchiesa/work/projects/2026-02-dafny-liftings/dataset/0121_1370_A/task.dfy

```dafny
ghost function Gcd(a: int, b: int): int
  requires a > 0 && b > 0
  decreases b
{
  if a % b == 0 then b
  else Gcd(b, a % b)
}

method MaximumGCD(n: int) returns (result: int)
  requires n >= 2
  ensures exists a: int | 1 <= a && a < n :: exists b: int | a < b && b <= n :: Gcd(a, b) == result
  ensures forall a: int | 1 <= a && a < n :: forall b: int | a < b && b <= n :: Gcd(a, b) <= result
{
  result := n / 2;
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
   /opt/homebrew/Cellar/dotnet@8/8.0.124/libexec/dotnet /Users/mchiesa/work/projects/2026-02-dafny-liftings/dafny-source/Binaries/Dafny.dll verify /Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0121_1370_A/verified.dfy --verification-time-limit 60
   ```

5. If verification fails, read the error, fix the code, and retry.

6. Write the final result to `/Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0121_1370_A/verified.dfy`.
   Also write `/Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0121_1370_A/verify_result.json`:
   ```json
   {
     "verified": true/false,
     "attempts": N,
     "error": "last error if failed, null if verified"
   }
   ```

7. If you cannot verify after several attempts, save your best attempt as verified.dfy
   and set "verified": false in the result JSON.

IMPORTANT: Write output files to /Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0121_1370_A/ (create the directory if needed).

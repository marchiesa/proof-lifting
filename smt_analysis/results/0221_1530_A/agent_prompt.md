Make this Dafny program verify. Add loop invariants, assertions, ghost variables,
and/or lemmas as needed. Do NOT modify the ghost spec (functions, predicates) or the method
signature (requires, ensures). Only add proof annotations inside method bodies.

## Problem: Binary Decimal
Let's call a number a binary decimal if it's a positive integer and all digits in its decimal notation are either $$$0$$$ or $$$1$$$. For example, $$$1\,010\,111$$$ is a binary decimal, while $$$10\,201$$$ and $$$787\,788$$$ are not.

Given a number $$$n$$$, you are asked to represent $$$n$$$ as a sum of some (not necessarily distinct) binary decimals. Compute the smallest number of binary decimals required for that.

## File: /Users/mchiesa/work/projects/2026-02-dafny-liftings/dataset/0221_1530_A/task.dfy

```dafny
ghost function NumDigits(n: int): nat
  requires n > 0
  decreases n
{
  if n < 10 then 1 else 1 + NumDigits(n / 10)
}

ghost function Pow2(d: nat): nat
  decreases d
{
  if d == 0 then 1 else 2 * Pow2(d - 1)
}

// Interprets the binary representation of i as a decimal number.
// This bijectively enumerates all binary decimals (positive integers
// whose decimal digits are all 0 or 1).
// E.g., 5 (binary 101) -> 101, 7 (binary 111) -> 111
ghost function BinToDec(i: nat): nat
  decreases i
{
  if i == 0 then 0
  else BinToDec(i / 2) * 10 + i % 2
}

// Can n be expressed as a sum of exactly k binary decimals?
// Binary decimals are enumerated as BinToDec(i) for 1 <= i < bdBound.
ghost predicate CanDecompose(n: int, k: nat, bdBound: nat)
  decreases k
{
  if k == 0 then n == 0
  else exists i: nat :: i >= 1 &&
    BinToDec(i) <= n && CanDecompose(n - BinToDec(i), k - 1, bdBound)
}

method BinaryDecimal(n: int) returns (result: int)
  requires n > 0
  ensures result >= 1
  ensures CanDecompose(n, result, Pow2(NumDigits(n)))
  ensures forall k | 0 <= k < result :: !CanDecompose(n, k, Pow2(NumDigits(n)))
{
  result := 0;
  var num := n;
  while num > 0 {
    var digit := num % 10;
    if digit > result {
      result := digit;
    }
    num := num / 10;
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
   /opt/homebrew/Cellar/dotnet@8/8.0.124/libexec/dotnet /Users/mchiesa/work/projects/2026-02-dafny-liftings/dafny-source/Binaries/Dafny.dll verify /Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0221_1530_A/verified.dfy --verification-time-limit 60
   ```

5. If verification fails, read the error, fix the code, and retry.

6. Write the final result to `/Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0221_1530_A/verified.dfy`.
   Also write `/Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0221_1530_A/verify_result.json`:
   ```json
   {
     "verified": true/false,
     "attempts": N,
     "error": "last error if failed, null if verified"
   }
   ```

7. If you cannot verify after several attempts, save your best attempt as verified.dfy
   and set "verified": false in the result JSON.

IMPORTANT: Write output files to /Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0221_1530_A/ (create the directory if needed).

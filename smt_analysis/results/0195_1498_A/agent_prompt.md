Make this Dafny program verify. Add loop invariants, assertions, ghost variables,
and/or lemmas as needed. Do NOT modify the ghost spec (functions, predicates) or the method
signature (requires, ensures). Only add proof annotations inside method bodies.

## Problem: GCD Sum
The $$$\text{$$$gcdSum$$$}$$$ of a positive integer is the $$$gcd$$$ of that integer with its sum of digits. Formally, $$$\text{$$$gcdSum$$$}(x) = gcd(x, \text{ sum of digits of } x)$$$ for a positive integer $$$x$$$. $$$gcd(a, b)$$$ denotes the greatest common divisor of $$$a$$$ and $$$b$$$ — the largest integer $$$d$$$ such that both integers $$$a$$$ and $$$b$$$ are divisible by $$$d$$$.

For example: $$$\text{$$$gcdSum$$$}(762) = gcd(762, 7 + 6 + 2)=gcd(762,15) = 3$$$.

Given an integer $$$n$$$, find the smallest integer $$$x \ge n$$$ such that $$$\text{$$$gcdSum$$$}(x) > 1$$$.

## File: /Users/mchiesa/work/projects/2026-02-dafny-liftings/dataset/0195_1498_A/task.dfy

```dafny
// ===== Specification: models the problem structure =====

ghost function Abs(n: int): nat
{
  if n >= 0 then n else -n
}

// Sum of the base-10 digits of a non-negative integer
ghost function DigitSum(n: int): nat
  requires n >= 0
  decreases n
{
  if n == 0 then 0
  else (n % 10) + DigitSum(n / 10)
}

// Largest d in {1..candidate} that divides both a and b; 0 if none
// Models the mathematical definition: gcd is the LARGEST common divisor
ghost function MaxCommonDivisor(a: int, b: int, candidate: int): nat
  requires a >= 0 && b >= 0 && candidate >= 0
  decreases candidate
{
  if candidate == 0 then 0
  else if a % candidate == 0 && b % candidate == 0 then candidate
  else MaxCommonDivisor(a, b, candidate - 1)
}

// gcd(a, b) = largest positive integer dividing both a and b
// gcd(0, 0) = 0 by convention
ghost function GcdSpec(a: int, b: int): nat
  requires a >= 0 && b >= 0
{
  if a == 0 && b == 0 then 0
  else MaxCommonDivisor(a, b, a + b)
}

// gcdSum(x) = gcd(x, digit_sum(x))
ghost function GcdSumOf(x: int): nat
  requires x >= 0
{
  GcdSpec(x, DigitSum(x))
}

// ===== Methods with specification =====

method Gcd(a: int, b: int) returns (g: int)
  ensures g == GcdSpec(Abs(a), Abs(b))
  decreases *
{
  var x := a;
  var y := b;
  if x < 0 { x := -x; }
  if y < 0 { y := -y; }
  while y != 0
    decreases *
  {
    var temp := y;
    y := x % y;
    x := temp;
  }
  g := x;
}

method GcdSum(n: int) returns (x: int)
  requires n >= 1
  ensures x >= n
  ensures GcdSumOf(x) > 1
  ensures forall y | n <= y < x :: GcdSumOf(y) <= 1
  decreases *
{
  x := n;
  while true
    decreases *
  {
    var digitSum := 0;
    var temp := x;
    if temp < 0 { temp := -temp; }
    while temp > 0
      decreases *
    {
      digitSum := digitSum + (temp % 10);
      temp := temp / 10;
    }
    var g := Gcd(digitSum, x);
    if g > 1 {
      return;
    }
    x := x + 1;
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
   /opt/homebrew/Cellar/dotnet@8/8.0.124/libexec/dotnet /Users/mchiesa/work/projects/2026-02-dafny-liftings/dafny-source/Binaries/Dafny.dll verify /Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0195_1498_A/verified.dfy --verification-time-limit 60
   ```

5. If verification fails, read the error, fix the code, and retry.

6. Write the final result to `/Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0195_1498_A/verified.dfy`.
   Also write `/Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0195_1498_A/verify_result.json`:
   ```json
   {
     "verified": true/false,
     "attempts": N,
     "error": "last error if failed, null if verified"
   }
   ```

7. If you cannot verify after several attempts, save your best attempt as verified.dfy
   and set "verified": false in the result JSON.

IMPORTANT: Write output files to /Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0195_1498_A/ (create the directory if needed).

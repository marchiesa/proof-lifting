Make this Dafny program verify. Add loop invariants, assertions, ghost variables,
and/or lemmas as needed. Do NOT modify the ghost spec (functions, predicates) or the method
signature (requires, ensures). Only add proof annotations inside method bodies.

## Problem: Potion-making
You have an initially empty cauldron, and you want to brew a potion in it. The potion consists of two ingredients: magic essence and water. The potion you want to brew should contain exactly $$$k\ \%$$$ magic essence and $$$(100 - k)\ \%$$$ water.

In one step, you can pour either one liter of magic essence or one liter of water into the cauldron. What is the minimum number of steps to brew a potion? You don't care about the total volume of the potion, only about the ratio between magic essence and water in it.

A small reminder: if you pour $$$e$$$ liters of essence and $$$w$$$ liters of water ($$$e + w > 0$$$) into the cauldron, then it contains $$$\frac{e}{e + w} \cdot 100\ \%$$$ (without rounding) magic essence and $$$\frac{w}{e + w} \cdot 100\ \%$$$ water.

## File: /Users/mchiesa/work/projects/2026-02-dafny-liftings/dataset/0219_1525_A/task.dfy

```dafny
// --- Specification: models the problem's structure directly ---

// d is a positive divisor of n
ghost predicate Divides(d: int, n: int)
{
  d > 0 && n % d == 0
}

// g is the greatest common divisor of a and b
ghost predicate IsGcd(g: int, a: int, b: int)
{
  g > 0 && a > 0 && b > 0 &&
  Divides(g, a) && Divides(g, b) &&
  forall d | 1 <= d <= a :: (Divides(d, a) && Divides(d, b)) ==> d <= g
}

// Pouring e liters of essence and w liters of water yields exactly k% essence
ghost predicate IsValidPotion(e: int, w: int, k: int)
{
  e >= 0 && w >= 0 && e + w > 0 && e * 100 == k * (e + w)
}

// There exists a way to pour exactly 'steps' total liters achieving k% essence
ghost predicate AchievableInSteps(steps: int, k: int)
{
  steps >= 0 &&
  exists e | 0 <= e <= steps :: IsValidPotion(e, steps - e, k)
}

// 'steps' is the minimum number of pours to achieve exactly k% essence
ghost predicate IsMinSteps(steps: int, k: int)
{
  steps >= 1 &&
  AchievableInSteps(steps, k) &&
  forall s | 1 <= s < steps :: !AchievableInSteps(s, k)
}

// --- Methods with specifications ---

method Gcd(a: int, b: int) returns (r: int)
  requires a > 0 && b > 0
  ensures IsGcd(r, a, b)
{
  var x := a;
  var y := b;
  while y != 0
  {
    var tmp := y;
    y := x % y;
    x := tmp;
  }
  r := x;
}

method PotionMaking(k: int) returns (steps: int)
  requires 1 <= k <= 100
  ensures IsMinSteps(steps, k)
{
  var g := Gcd(k, 100);
  steps := 100 / g;
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
   /opt/homebrew/Cellar/dotnet@8/8.0.124/libexec/dotnet /Users/mchiesa/work/projects/2026-02-dafny-liftings/dafny-source/Binaries/Dafny.dll verify /Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0219_1525_A/verified.dfy --verification-time-limit 60
   ```

5. If verification fails, read the error, fix the code, and retry.

6. Write the final result to `/Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0219_1525_A/verified.dfy`.
   Also write `/Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0219_1525_A/verify_result.json`:
   ```json
   {
     "verified": true/false,
     "attempts": N,
     "error": "last error if failed, null if verified"
   }
   ```

7. If you cannot verify after several attempts, save your best attempt as verified.dfy
   and set "verified": false in the result JSON.

IMPORTANT: Write output files to /Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0219_1525_A/ (create the directory if needed).

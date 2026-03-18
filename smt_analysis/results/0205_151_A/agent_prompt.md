Make this Dafny program verify. Add loop invariants, assertions, ghost variables,
and/or lemmas as needed. Do NOT modify the ghost spec (functions, predicates) or the method
signature (requires, ensures). Only add proof annotations inside method bodies.

## Problem: Soft Drinking
This winter is so cold in Nvodsk! A group of n friends decided to buy k bottles of a soft drink called "Take-It-Light" to warm up a bit. Each bottle has l milliliters of the drink. Also they bought c limes and cut each of them into d slices. After that they found p grams of salt.

To make a toast, each friend needs nl milliliters of the drink, a slice of lime and np grams of salt. The friends want to make as many toasts as they can, provided they all drink the same amount. How many toasts can each friend make?

## File: /Users/mchiesa/work/projects/2026-02-dafny-liftings/dataset/0205_151_A/task.dfy

```dafny
ghost predicate Feasible(n: int, k: int, l: int, c: int, d: int, p: int, nl: int, np: int, t: int)
{
  t >= 0 &&
  n * t * nl <= k * l &&
  n * t <= c * d &&
  n * t * np <= p
}

method SoftDrinking(n: int, k: int, l: int, c: int, d: int, p: int, nl: int, np: int) returns (toasts: int)
  requires n >= 1
  requires k >= 0 && l >= 0
  requires c >= 0 && d >= 0
  requires p >= 0
  requires nl >= 1
  requires np >= 1
  ensures Feasible(n, k, l, c, d, p, nl, np, toasts)
  ensures !Feasible(n, k, l, c, d, p, nl, np, toasts + 1)
{
  var totalDrink := k * l;
  var drinksPossible := totalDrink / nl;
  var limePieces := c * d;
  if limePieces < drinksPossible {
    drinksPossible := limePieces;
  }
  var saltServings := p / np;
  if saltServings < drinksPossible {
    drinksPossible := saltServings;
  }
  toasts := drinksPossible / n;
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
   /opt/homebrew/Cellar/dotnet@8/8.0.124/libexec/dotnet /Users/mchiesa/work/projects/2026-02-dafny-liftings/dafny-source/Binaries/Dafny.dll verify /Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0205_151_A/verified.dfy --verification-time-limit 60
   ```

5. If verification fails, read the error, fix the code, and retry.

6. Write the final result to `/Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0205_151_A/verified.dfy`.
   Also write `/Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0205_151_A/verify_result.json`:
   ```json
   {
     "verified": true/false,
     "attempts": N,
     "error": "last error if failed, null if verified"
   }
   ```

7. If you cannot verify after several attempts, save your best attempt as verified.dfy
   and set "verified": false in the result JSON.

IMPORTANT: Write output files to /Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0205_151_A/ (create the directory if needed).

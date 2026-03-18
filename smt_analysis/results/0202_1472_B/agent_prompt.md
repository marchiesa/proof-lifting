Make this Dafny program verify. Add loop invariants, assertions, ghost variables,
and/or lemmas as needed. Do NOT modify the ghost spec (functions, predicates) or the method
signature (requires, ensures). Only add proof annotations inside method bodies.

## Problem: Fair Division
Alice and Bob received $$$n$$$ candies from their parents. Each candy weighs either 1 gram or 2 grams. Now they want to divide all candies among themselves fairly so that the total weight of Alice's candies is equal to the total weight of Bob's candies.

Check if they can do that.

Note that candies are not allowed to be cut in half.

## File: /Users/mchiesa/work/projects/2026-02-dafny-liftings/dataset/0202_1472_B/task.dfy

```dafny
// --- Specification: models the problem structure ---

// Sum of all candy weights
ghost function Sum(a: seq<int>): int
  decreases |a|
{
  if |a| == 0 then 0 else Sum(a[..|a|-1]) + a[|a|-1]
}

// 2^exp: size of the assignment space for exp candies
ghost function Pow2(exp: nat): nat
  decreases exp
{
  if exp == 0 then 1 else 2 * Pow2(exp - 1)
}

// Extract bit i from a bitmask (0 = least significant)
ghost function Bit(mask: nat, i: nat): bool
  decreases i
{
  if i == 0 then mask % 2 == 1
  else Bit(mask / 2, i - 1)
}

// Total weight of candies assigned to Alice (bit = 1) under assignment `mask`
ghost function AliceWeight(a: seq<int>, mask: nat): int
  decreases |a|
{
  if |a| == 0 then 0
  else AliceWeight(a[..|a|-1], mask) + (if Bit(mask, |a| - 1) then a[|a|-1] else 0)
}

// Total weight of candies assigned to Bob (bit = 0) under assignment `mask`
ghost function BobWeight(a: seq<int>, mask: nat): int
  decreases |a|
{
  if |a| == 0 then 0
  else BobWeight(a[..|a|-1], mask) + (if !Bit(mask, |a| - 1) then a[|a|-1] else 0)
}

// There exists an assignment of all candies to Alice and Bob
// such that Alice's total weight equals Bob's total weight
ghost predicate CanDivideFairly(a: seq<int>)
{
  exists mask: nat ::
    AliceWeight(a, mask) == BobWeight(a, mask)
}

// --- Method with specification ---

method FairDivision(a: seq<int>) returns (result: bool)
  requires forall i | 0 <= i < |a| :: a[i] == 1 || a[i] == 2
  ensures result == CanDivideFairly(a)
{
  var s := 0;
  var count1 := 0;
  var count2 := 0;
  var i := 0;
  while i < |a|
  {
    s := s + a[i];
    if a[i] == 1 {
      count1 := count1 + 1;
    }
    if a[i] == 2 {
      count2 := count2 + 1;
    }
    i := i + 1;
  }
  if s % 2 == 1 {
    return false;
  }
  if count2 % 2 == 1 && count1 == 0 {
    return false;
  }
  return true;
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
   /opt/homebrew/Cellar/dotnet@8/8.0.124/libexec/dotnet /Users/mchiesa/work/projects/2026-02-dafny-liftings/dafny-source/Binaries/Dafny.dll verify /Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0202_1472_B/verified.dfy --verification-time-limit 60
   ```

5. If verification fails, read the error, fix the code, and retry.

6. Write the final result to `/Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0202_1472_B/verified.dfy`.
   Also write `/Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0202_1472_B/verify_result.json`:
   ```json
   {
     "verified": true/false,
     "attempts": N,
     "error": "last error if failed, null if verified"
   }
   ```

7. If you cannot verify after several attempts, save your best attempt as verified.dfy
   and set "verified": false in the result JSON.

IMPORTANT: Write output files to /Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0202_1472_B/ (create the directory if needed).

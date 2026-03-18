Make this Dafny program verify. Add loop invariants, assertions, ghost variables,
and/or lemmas as needed. Do NOT modify the ghost spec (functions, predicates) or the method
signature (requires, ensures). Only add proof annotations inside method bodies.

## Problem: Splitting into digits
Vasya has his favourite number $$$n$$$. He wants to split it to some non-zero digits. It means, that he wants to choose some digits $$$d_1, d_2, \ldots, d_k$$$, such that $$$1 \leq d_i \leq 9$$$ for all $$$i$$$ and $$$d_1 + d_2 + \ldots + d_k = n$$$.

Vasya likes beauty in everything, so he wants to find any solution with the minimal possible number of different digits among $$$d_1, d_2, \ldots, d_k$$$. Help him!

## File: /Users/mchiesa/work/projects/2026-02-dafny-liftings/dataset/0055_1104_A/task.dfy

```dafny
// === Specification predicates and functions ===

ghost function Sum(a: seq<int>): int
  decreases |a|
{
  if |a| == 0 then 0 else a[|a| - 1] + Sum(a[..|a| - 1])
}

ghost predicate AllInRange(a: seq<int>, lo: int, hi: int)
{
  forall i | 0 <= i < |a| :: lo <= a[i] <= hi
}

ghost function DistinctSet(a: seq<int>): set<int>
  decreases |a|
{
  if |a| == 0 then {} else {a[|a| - 1]} + DistinctSet(a[..|a| - 1])
}

ghost function CountDistinct(a: seq<int>): int
{
  |DistinctSet(a)|
}

// A valid splitting of n: non-empty sequence of digits 1..9 summing to n
ghost predicate IsValidSplitting(a: seq<int>, n: int)
{
  |a| >= 1 && AllInRange(a, 1, 9) && Sum(a) == n
}

ghost function Pow2(e: int): int
  requires e >= 0
  ensures Pow2(e) >= 1
  decreases e
{
  if e == 0 then 1 else 2 * Pow2(e - 1)
}

ghost function PopCount(mask: int): int
  requires mask >= 0
  ensures PopCount(mask) >= 0
  decreases mask
{
  if mask == 0 then 0 else PopCount(mask / 2) + mask % 2
}

// Can n be expressed as a non-negative integer combination of the
// digit values v..9 whose bits are set in mask?
// Bit (v-1) of mask indicates whether digit value v is allowed.
ghost predicate CanMakeSumFrom(n: int, mask: int, v: int)
  requires n >= 0 && mask >= 0 && 1 <= v <= 10
  decreases 10 - v
{
  if v == 10 then
    n == 0
  else if (mask / Pow2(v - 1)) % 2 == 0 then
    CanMakeSumFrom(n, mask, v + 1)
  else
    exists c | 0 <= c <= n / v :: CanMakeSumFrom(n - c * v, mask, v + 1)
}

// Can n be expressed as a sum of digits from the subset of {1..9} encoded by mask?
ghost predicate CanMakeSum(n: int, mask: int)
  requires n >= 0 && 0 <= mask < 512
{
  CanMakeSumFrom(n, mask, 1)
}

// Can n be split into digits 1..9 using at most d distinct digit values?
ghost predicate CanSplitWithAtMost(n: int, d: int)
  requires n >= 0
{
  exists mask | 0 <= mask < 512 ::
    PopCount(mask) <= d && CanMakeSum(n, mask)
}

// === Method with formal specification ===

method SplitIntoDigits(n: int) returns (k: int, digits: seq<int>)
  requires n >= 1
  ensures k == |digits|
  ensures IsValidSplitting(digits, n)
  ensures !CanSplitWithAtMost(n, CountDistinct(digits) - 1)
{
  k := n;
  digits := seq(n, _ => 1);
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
   /opt/homebrew/Cellar/dotnet@8/8.0.124/libexec/dotnet /Users/mchiesa/work/projects/2026-02-dafny-liftings/dafny-source/Binaries/Dafny.dll verify /Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0055_1104_A/verified.dfy --verification-time-limit 60
   ```

5. If verification fails, read the error, fix the code, and retry.

6. Write the final result to `/Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0055_1104_A/verified.dfy`.
   Also write `/Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0055_1104_A/verify_result.json`:
   ```json
   {
     "verified": true/false,
     "attempts": N,
     "error": "last error if failed, null if verified"
   }
   ```

7. If you cannot verify after several attempts, save your best attempt as verified.dfy
   and set "verified": false in the result JSON.

IMPORTANT: Write output files to /Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0055_1104_A/ (create the directory if needed).

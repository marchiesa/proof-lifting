Make this Dafny program verify. Add loop invariants, assertions, ghost variables,
and/or lemmas as needed. Do NOT modify the ghost spec (functions, predicates) or the method
signature (requires, ensures). Only add proof annotations inside method bodies.

## Problem: Boring Apartments
There is a building consisting of $$$10~000$$$ apartments numbered from $$$1$$$ to $$$10~000$$$, inclusive.

Call an apartment boring, if its number consists of the same digit. Examples of boring apartments are $$$11, 2, 777, 9999$$$ and so on.

Our character is a troublemaker, and he calls the intercoms of all boring apartments, till someone answers the call, in the following order:

- First he calls all apartments consisting of digit $$$1$$$, in increasing order ($$$1, 11, 111, 1111$$$).
- Next he calls all apartments consisting of digit $$$2$$$, in increasing order ($$$2, 22, 222, 2222$$$)
- And so on.

The resident of the boring apartment $$$x$$$ answers the call, and our character stops calling anyone further.

Our character wants to know how many digits he pressed in total and your task is to help him to count the total number of keypresses.

For example, if the resident of boring apartment $$$22$$$ answered, then our character called apartments with numbers $$$1, 11, 111, 1111, 2, 22$$$ and the total number of digits he pressed is $$$1 + 2 + 3 + 4 + 1 + 2 = 13$$$.

You have to answer $$$t$$$ independent test cases.

## File: /Users/mchiesa/work/projects/2026-02-dafny-liftings/dataset/0175_1433_A/task.dfy

```dafny
// Number of digits in a positive integer
ghost function NumDigits(n: int): int
  requires n >= 1
  decreases n
{
  if n < 10 then 1 else 1 + NumDigits(n / 10)
}

// RepUnit(k) = 111...1 (k ones) — the repeating-ones template
ghost function RepUnit(k: int): int
  requires 1 <= k <= 4
{
  if k == 1 then 1 else 10 * RepUnit(k - 1) + 1
}

// The boring apartment number formed by repeating digit d exactly k times
ghost function BoringNum(d: int, k: int): int
  requires 1 <= d <= 9 && 1 <= k <= 4
{
  d * RepUnit(k)
}

// x is a boring apartment if it equals BoringNum(d, k) for some valid d, k
ghost predicate IsBoringApartment(x: int)
{
  exists d {:trigger BoringNum(d, 1)} | 1 <= d <= 9 ::
    exists k {:trigger BoringNum(d, k)} | 1 <= k <= 4 :: x == BoringNum(d, k)
}

// Total keypresses when calling all boring apartments in order
// (1,1), (1,2), (1,3), (1,4), (2,1), ..., up to and including (d, k).
// Each apartment contributes NumDigits(its number) keypresses.
ghost function TotalKeypresses(d: int, k: int): int
  requires 1 <= d <= 9 && 1 <= k <= 4
  decreases 4 * (d - 1) + (k - 1)
{
  var cost := NumDigits(BoringNum(d, k));
  if d == 1 && k == 1 then cost
  else if k > 1 then TotalKeypresses(d, k - 1) + cost
  else TotalKeypresses(d - 1, 4) + cost
}

method BoringApartments(x: int) returns (keypresses: int)
  requires IsBoringApartment(x)
  ensures exists d {:trigger BoringNum(d, 1)} | 1 <= d <= 9 ::
    exists k {:trigger BoringNum(d, k)} | 1 <= k <= 4 ::
    x == BoringNum(d, k) && keypresses == TotalKeypresses(d, k)
{
  // ... original body unchanged ...
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
   /opt/homebrew/Cellar/dotnet@8/8.0.124/libexec/dotnet /Users/mchiesa/work/projects/2026-02-dafny-liftings/dafny-source/Binaries/Dafny.dll verify /Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0175_1433_A/verified.dfy --verification-time-limit 60
   ```

5. If verification fails, read the error, fix the code, and retry.

6. Write the final result to `/Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0175_1433_A/verified.dfy`.
   Also write `/Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0175_1433_A/verify_result.json`:
   ```json
   {
     "verified": true/false,
     "attempts": N,
     "error": "last error if failed, null if verified"
   }
   ```

7. If you cannot verify after several attempts, save your best attempt as verified.dfy
   and set "verified": false in the result JSON.

IMPORTANT: Write output files to /Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0175_1433_A/ (create the directory if needed).

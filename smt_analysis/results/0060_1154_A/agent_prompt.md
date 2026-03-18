Make this Dafny program verify. Add loop invariants, assertions, ghost variables,
and/or lemmas as needed. Do NOT modify the ghost spec (functions, predicates) or the method
signature (requires, ensures). Only add proof annotations inside method bodies.

## Problem: Restoring Three Numbers
Polycarp has guessed three positive integers $$$a$$$, $$$b$$$ and $$$c$$$. He keeps these numbers in secret, but he writes down four numbers on a board in arbitrary order — their pairwise sums (three numbers) and sum of all three numbers (one number). So, there are four numbers on a board in random order: $$$a+b$$$, $$$a+c$$$, $$$b+c$$$ and $$$a+b+c$$$.

You have to guess three numbers $$$a$$$, $$$b$$$ and $$$c$$$ using given numbers. Print three guessed integers in any order.

Pay attention that some given numbers $$$a$$$, $$$b$$$ and $$$c$$$ can be equal (it is also possible that $$$a=b=c$$$).

## File: /Users/mchiesa/work/projects/2026-02-dafny-liftings/dataset/0060_1154_A/task.dfy

```dafny
ghost function RemoveIndex(s: seq<int>, m: int): seq<int>
  requires 0 <= m < |s|
  ensures |RemoveIndex(s, m)| == |s| - 1
{
  s[..m] + s[m+1..]
}

// Core postcondition: a, b, c are positive and their pairwise sums
// plus total sum form exactly the input (in any order).
ghost predicate IsValidRestoration(x: seq<int>, a: int, b: int, c: int)
{
  |x| == 4 &&
  a > 0 && b > 0 && c > 0 &&
  multiset{a + b, a + c, b + c, a + b + c} == multiset(x)
}

// Compilable precondition: the input admits some valid (a, b, c).
// Since a+b+c > any pairwise sum when a,b,c > 0, the total must be
// one of the four elements — so we enumerate the 4 candidates.
ghost predicate HasValidRestoration(x: seq<int>)
  requires |x| == 4
{
  exists m | 0 <= m < 4 ::
    var rest := RemoveIndex(x, m);
    var a := x[m] - rest[0];
    var b := x[m] - rest[1];
    var c := x[m] - rest[2];
    a > 0 && b > 0 && c > 0 &&
    multiset{a + b, a + c, b + c, a + b + c} == multiset(x)
}

method RestoreThreeNumbers(x: seq<int>) returns (a: int, b: int, c: int)
  requires |x| == 4
  requires HasValidRestoration(x)
  ensures IsValidRestoration(x, a, b, c)
{
  var maxVal := x[0];
  var i := 1;
  while i < |x|
  {
    if x[i] > maxVal {
      maxVal := x[i];
    }
    i := i + 1;
  }

  var result: seq<int> := [];
  i := 0;
  while i < |x|
  {
    if x[i] != maxVal {
      result := result + [maxVal - x[i]];
    }
    i := i + 1;
  }

  a := result[0];
  b := result[1];
  c := result[2];
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
   /opt/homebrew/Cellar/dotnet@8/8.0.124/libexec/dotnet /Users/mchiesa/work/projects/2026-02-dafny-liftings/dafny-source/Binaries/Dafny.dll verify /Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0060_1154_A/verified.dfy --verification-time-limit 60
   ```

5. If verification fails, read the error, fix the code, and retry.

6. Write the final result to `/Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0060_1154_A/verified.dfy`.
   Also write `/Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0060_1154_A/verify_result.json`:
   ```json
   {
     "verified": true/false,
     "attempts": N,
     "error": "last error if failed, null if verified"
   }
   ```

7. If you cannot verify after several attempts, save your best attempt as verified.dfy
   and set "verified": false in the result JSON.

IMPORTANT: Write output files to /Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0060_1154_A/ (create the directory if needed).

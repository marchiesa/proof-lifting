Make this Dafny program verify. Add loop invariants, assertions, ghost variables,
and/or lemmas as needed. Do NOT modify the ghost spec (functions, predicates) or the method
signature (requires, ensures). Only add proof annotations inside method bodies.

## Problem: Finding Sasuke
Naruto has sneaked into the Orochimaru's lair and is now looking for Sasuke. There are $$$T$$$ rooms there. Every room has a door into it, each door can be described by the number $$$n$$$ of seals on it and their integer energies $$$a_1$$$, $$$a_2$$$, ..., $$$a_n$$$. All energies $$$a_i$$$ are nonzero and do not exceed $$$100$$$ by absolute value. Also, $$$n$$$ is even.

In order to open a door, Naruto must find such $$$n$$$ seals with integer energies $$$b_1$$$, $$$b_2$$$, ..., $$$b_n$$$ that the following equality holds: $$$a_{1} \cdot b_{1} + a_{2} \cdot b_{2} + ... + a_{n} \cdot b_{n} = 0$$$. All $$$b_i$$$ must be nonzero as well as $$$a_i$$$ are, and also must not exceed $$$100$$$ by absolute value. Please find required seals for every room there.

## File: /Users/mchiesa/work/projects/2026-02-dafny-liftings/dataset/0138_1413_A/task.dfy

```dafny
ghost function DotProduct(a: seq<int>, b: seq<int>): int
  requires |a| == |b|
  decreases |a|
{
  if |a| == 0 then 0
  else DotProduct(a[..|a|-1], b[..|b|-1]) + a[|a|-1] * b[|b|-1]
}

ghost predicate AllNonZero(s: seq<int>) {
  forall i | 0 <= i < |s| :: s[i] != 0
}

ghost predicate AllBounded(s: seq<int>, bound: int) {
  forall i | 0 <= i < |s| :: -bound <= s[i] <= bound
}

ghost predicate ValidSolution(a: seq<int>, b: seq<int>) {
  |a| == |b|
  && AllNonZero(b)
  && AllBounded(b, 100)
  && DotProduct(a, b) == 0
}

method FindSasuke(a: seq<int>) returns (b: seq<int>)
  requires |a| % 2 == 0
  requires AllNonZero(a)
  requires AllBounded(a, 100)
  ensures ValidSolution(a, b)
{
  b := [];
  var i := 0;
  while i < |a|
  {
    if i % 2 == 0 {
      b := b + [a[i + 1]];
    } else {
      b := b + [-a[i - 1]];
    }
    i := i + 1;
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
   /opt/homebrew/Cellar/dotnet@8/8.0.124/libexec/dotnet /Users/mchiesa/work/projects/2026-02-dafny-liftings/dafny-source/Binaries/Dafny.dll verify /Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0138_1413_A/verified.dfy --verification-time-limit 60
   ```

5. If verification fails, read the error, fix the code, and retry.

6. Write the final result to `/Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0138_1413_A/verified.dfy`.
   Also write `/Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0138_1413_A/verify_result.json`:
   ```json
   {
     "verified": true/false,
     "attempts": N,
     "error": "last error if failed, null if verified"
   }
   ```

7. If you cannot verify after several attempts, save your best attempt as verified.dfy
   and set "verified": false in the result JSON.

IMPORTANT: Write output files to /Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0138_1413_A/ (create the directory if needed).

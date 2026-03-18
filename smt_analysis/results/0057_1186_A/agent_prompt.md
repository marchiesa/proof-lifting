Make this Dafny program verify. Add loop invariants, assertions, ghost variables,
and/or lemmas as needed. Do NOT modify the ghost spec (functions, predicates) or the method
signature (requires, ensures). Only add proof annotations inside method bodies.

## Problem: Vus the Cossack and a Contest
Vus the Cossack holds a programming competition, in which $$$n$$$ people participate. He decided to award them all with pens and notebooks. It is known that Vus has exactly $$$m$$$ pens and $$$k$$$ notebooks.

Determine whether the Cossack can reward all participants, giving each of them at least one pen and at least one notebook.

## File: /Users/mchiesa/work/projects/2026-02-dafny-liftings/dataset/0057_1186_A/task.dfy

```dafny
// --- Specification: Vus the Cossack and a Contest ---

// Sum of all elements in a sequence
ghost function SumSeq(s: seq<int>): int
  decreases |s|
{
  if |s| == 0 then 0 else SumSeq(s[..|s|-1]) + s[|s|-1]
}

// Every person receives at least one item
ghost predicate AllAtLeastOne(s: seq<int>)
{
  forall i | 0 <= i < |s| :: s[i] >= 1
}

// A valid distribution of `supply` items among `n` people, each getting at least 1
ghost predicate ValidDistribution(dist: seq<int>, n: int, supply: int)
{
  n >= 0 &&
  |dist| == n &&
  AllAtLeastOne(dist) &&
  SumSeq(dist) <= supply
}

// A valid rewarding: valid distributions of both pens and notebooks
ghost predicate ValidRewarding(penDist: seq<int>, noteDist: seq<int>, n: int, m: int, k: int)
{
  ValidDistribution(penDist, n, m) && ValidDistribution(noteDist, n, k)
}

// The minimal-cost distribution: give exactly 1 item to each person
ghost function UniformDist(n: nat): (r: seq<int>)
  ensures |r| == n
  ensures forall i | 0 <= i < n :: r[i] == 1
  ensures SumSeq(r) == n
  decreases n
{
  if n == 0 then [] else UniformDist(n - 1) + [1]
}

// Mathematical fact: any distribution giving everyone >= 1 item uses >= n items total.
// This proves UniformDist is optimal, so if it fails, no distribution can succeed.
ghost function SumLowerBound(s: seq<int>): (b: bool)
  ensures AllAtLeastOne(s) ==> SumSeq(s) >= |s|
  decreases |s|
{
  if |s| == 0 then true
  else var _ := SumLowerBound(s[..|s|-1]); true
}

method VusContest(n: int, m: int, k: int) returns (result: string)
  requires n >= 1
  ensures result == "Yes" || result == "No"
  ensures result == "Yes" <==> ValidRewarding(UniformDist(n), UniformDist(n), n, m, k)
{
  if k < n || m < n {
    result := "No";
  } else {
    result := "Yes";
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
   /opt/homebrew/Cellar/dotnet@8/8.0.124/libexec/dotnet /Users/mchiesa/work/projects/2026-02-dafny-liftings/dafny-source/Binaries/Dafny.dll verify /Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0057_1186_A/verified.dfy --verification-time-limit 60
   ```

5. If verification fails, read the error, fix the code, and retry.

6. Write the final result to `/Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0057_1186_A/verified.dfy`.
   Also write `/Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0057_1186_A/verify_result.json`:
   ```json
   {
     "verified": true/false,
     "attempts": N,
     "error": "last error if failed, null if verified"
   }
   ```

7. If you cannot verify after several attempts, save your best attempt as verified.dfy
   and set "verified": false in the result JSON.

IMPORTANT: Write output files to /Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0057_1186_A/ (create the directory if needed).

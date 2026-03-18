Make this Dafny program verify. Add loop invariants, assertions, ghost variables,
and/or lemmas as needed. Do NOT modify the ghost spec (functions, predicates) or the method
signature (requires, ensures). Only add proof annotations inside method bodies.

## Problem: Neko Finds Grapes
On a random day, Neko found $$$n$$$ treasure chests and $$$m$$$ keys. The $$$i$$$-th chest has an integer $$$a_i$$$ written on it and the $$$j$$$-th key has an integer $$$b_j$$$ on it. Neko knows those chests contain the powerful mysterious green Grapes, thus Neko wants to open as many treasure chests as possible.

The $$$j$$$-th key can be used to unlock the $$$i$$$-th chest if and only if the sum of the key number and the chest number is an odd number. Formally, $$$a_i + b_j \equiv 1 \pmod{2}$$$. One key can be used to open at most one chest, and one chest can be opened at most once.

Find the maximum number of chests Neko can open.

## File: /Users/mchiesa/work/projects/2026-02-dafny-liftings/dataset/0042_1152_A/task.dfy

```dafny
// --- Specification: maximum bipartite matching under odd-sum constraint ---

ghost function CountEven(s: seq<int>): int
  decreases |s|
{
  if |s| == 0 then 0
  else CountEven(s[..|s|-1]) + (if s[|s|-1] % 2 == 0 then 1 else 0)
}

ghost function CountOdd(s: seq<int>): int
  decreases |s|
{
  if |s| == 0 then 0
  else CountOdd(s[..|s|-1]) + (if s[|s|-1] % 2 != 0 then 1 else 0)
}

ghost function Min(x: int, y: int): int
{
  if x <= y then x else y
}

// Collect indices of even-valued elements
ghost function EvenIndices(s: seq<int>): seq<int>
  decreases |s|
{
  if |s| == 0 then []
  else EvenIndices(s[..|s|-1]) + (if s[|s|-1] % 2 == 0 then [|s|-1] else [])
}

// Collect indices of odd-valued elements
ghost function OddIndices(s: seq<int>): seq<int>
  decreases |s|
{
  if |s| == 0 then []
  else OddIndices(s[..|s|-1]) + (if s[|s|-1] % 2 != 0 then [|s|-1] else [])
}

// Zip two index sequences into pairs, truncated to the shorter length
ghost function Zip(xs: seq<int>, ys: seq<int>): seq<(int, int)>
  decreases |xs|
{
  if |xs| == 0 || |ys| == 0 then []
  else [(xs[0], ys[0])] + Zip(xs[1..], ys[1..])
}

// A valid matching: pairs of (chest_index, key_index) where
//   - each pair satisfies a_i + b_j ≡ 1 (mod 2)
//   - no chest is opened twice, no key is used twice
ghost predicate IsValidMatching(a: seq<int>, b: seq<int>, m: seq<(int, int)>)
{
  (forall k | 0 <= k < |m| ::
    0 <= m[k].0 < |a| &&
    0 <= m[k].1 < |b| &&
    (a[m[k].0] + b[m[k].1]) % 2 == 1)
  &&
  (forall i | 0 <= i < |m| :: forall j | i + 1 <= j < |m| :: m[i].0 != m[j].0)
  &&
  (forall i | 0 <= i < |m| :: forall j | i + 1 <= j < |m| :: m[i].1 != m[j].1)
}

// Construct a witness matching: pair even chests with odd keys, odd chests with even keys
ghost function WitnessMatching(a: seq<int>, b: seq<int>): seq<(int, int)>
{
  Zip(EvenIndices(a), OddIndices(b)) + Zip(OddIndices(a), EvenIndices(b))
}

// Upper bound on any valid matching size: since each valid pair requires
// different parities, every matching decomposes into (even chest, odd key)
// pairs and (odd chest, even key) pairs, each independently bounded
ghost function MatchingUpperBound(a: seq<int>, b: seq<int>): int
{
  Min(CountEven(a), CountOdd(b)) + Min(CountOdd(a), CountEven(b))
}

method NekoFindsGrapes(a: seq<int>, b: seq<int>) returns (maxChests: int)
  // Achievability: a valid matching of size maxChests exists
  ensures IsValidMatching(a, b, WitnessMatching(a, b))
  ensures |WitnessMatching(a, b)| == maxChests
  // Optimality: maxChests equals the parity-based upper bound on any matching
  ensures maxChests == MatchingUpperBound(a, b)
{
  var a0 := 0;
  var a1 := 0;
  var b0 := 0;
  var b1 := 0;

  var i := 0;
  while i < |a|
  {
    if a[i] % 2 == 0 {
      a0 := a0 + 1;
    } else {
      a1 := a1 + 1;
    }
    i := i + 1;
  }

  i := 0;
  while i < |b|
  {
    if b[i] % 2 == 0 {
      b0 := b0 + 1;
    } else {
      b1 := b1 + 1;
    }
    i := i + 1;
  }

  var x := if a0 < b1 then a0 else b1;
  var y := if a1 < b0 then a1 else b0;
  maxChests := x + y;
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
   /opt/homebrew/Cellar/dotnet@8/8.0.124/libexec/dotnet /Users/mchiesa/work/projects/2026-02-dafny-liftings/dafny-source/Binaries/Dafny.dll verify /Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0042_1152_A/verified.dfy --verification-time-limit 60
   ```

5. If verification fails, read the error, fix the code, and retry.

6. Write the final result to `/Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0042_1152_A/verified.dfy`.
   Also write `/Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0042_1152_A/verify_result.json`:
   ```json
   {
     "verified": true/false,
     "attempts": N,
     "error": "last error if failed, null if verified"
   }
   ```

7. If you cannot verify after several attempts, save your best attempt as verified.dfy
   and set "verified": false in the result JSON.

IMPORTANT: Write output files to /Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0042_1152_A/ (create the directory if needed).

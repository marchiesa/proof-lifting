Make this Dafny program verify. Add loop invariants, assertions, ghost variables,
and/or lemmas as needed. Do NOT modify the ghost spec (functions, predicates) or the method
signature (requires, ensures). Only add proof annotations inside method bodies.

## Problem: Circle Coloring
You are given three sequences: $$$a_1, a_2, \ldots, a_n$$$; $$$b_1, b_2, \ldots, b_n$$$; $$$c_1, c_2, \ldots, c_n$$$.

For each $$$i$$$, $$$a_i \neq b_i$$$, $$$a_i \neq c_i$$$, $$$b_i \neq c_i$$$.

Find a sequence $$$p_1, p_2, \ldots, p_n$$$, that satisfy the following conditions:

- $$$p_i \in \{a_i, b_i, c_i\}$$$
- $$$p_i \neq p_{(i \mod n) + 1}$$$.

In other words, for each element, you need to choose one of the three possible values, such that no two adjacent elements (where we consider elements $$$i,i+1$$$ adjacent for $$$i<n$$$ and also elements $$$1$$$ and $$$n$$$) will have equal value.

It can be proved that in the given constraints solution always exists. You don't need to minimize/maximize anything, you need to find any proper sequence.

## File: /Users/mchiesa/work/projects/2026-02-dafny-liftings/dataset/0140_1408_A/task.dfy

```dafny
ghost predicate ValidInput(n: int, a: seq<int>, b: seq<int>, c: seq<int>)
{
  n >= 3 &&
  |a| == n && |b| == n && |c| == n &&
  forall i | 0 <= i < n :: a[i] != b[i] && a[i] != c[i] && b[i] != c[i]
}

ghost predicate ChosenFromOptions(p: seq<int>, a: seq<int>, b: seq<int>, c: seq<int>)
  requires |p| == |a| == |b| == |c|
{
  forall i | 0 <= i < |p| :: p[i] == a[i] || p[i] == b[i] || p[i] == c[i]
}

ghost predicate NoAdjacentEqual(p: seq<int>)
  requires |p| >= 1
{
  // Consecutive pairs
  (forall i | 0 <= i < |p| - 1 :: p[i] != p[i + 1]) &&
  // Circular wrap-around: last element != first element
  p[|p| - 1] != p[0]
}

ghost predicate ValidColoring(p: seq<int>, n: int, a: seq<int>, b: seq<int>, c: seq<int>)
{
  |p| == n && n >= 3 &&
  |a| == n && |b| == n && |c| == n &&
  ChosenFromOptions(p, a, b, c) &&
  NoAdjacentEqual(p)
}

method CircleColoring(n: int, a: seq<int>, b: seq<int>, c: seq<int>) returns (p: seq<int>)
  requires ValidInput(n, a, b, c)
  ensures ValidColoring(p, n, a, b, c)
{
  var out := new int[n];
  var i := 0;
  while i < n {
    out[i] := -1;
    i := i + 1;
  }
  i := 0;
  while i < n {
    var prev := (i - 1 + n) % n;
    var next := (i + 1) % n;
    if a[i] != out[prev] && a[i] != out[next] {
      out[i] := a[i];
    }
    if b[i] != out[prev] && b[i] != out[next] {
      out[i] := b[i];
    }
    if c[i] != out[prev] && c[i] != out[next] {
      out[i] := c[i];
    }
    i := i + 1;
  }
  p := out[..];
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
   /opt/homebrew/Cellar/dotnet@8/8.0.124/libexec/dotnet /Users/mchiesa/work/projects/2026-02-dafny-liftings/dafny-source/Binaries/Dafny.dll verify /Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0140_1408_A/verified.dfy --verification-time-limit 60
   ```

5. If verification fails, read the error, fix the code, and retry.

6. Write the final result to `/Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0140_1408_A/verified.dfy`.
   Also write `/Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0140_1408_A/verify_result.json`:
   ```json
   {
     "verified": true/false,
     "attempts": N,
     "error": "last error if failed, null if verified"
   }
   ```

7. If you cannot verify after several attempts, save your best attempt as verified.dfy
   and set "verified": false in the result JSON.

IMPORTANT: Write output files to /Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0140_1408_A/ (create the directory if needed).

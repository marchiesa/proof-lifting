Make this Dafny program verify. Add loop invariants, assertions, ghost variables,
and/or lemmas as needed. Do NOT modify the ghost spec (functions, predicates) or the method
signature (requires, ensures). Only add proof annotations inside method bodies.

## Problem: Petya and Origami
Petya is having a party soon, and he has decided to invite his $$$n$$$ friends.

He wants to make invitations in the form of origami. For each invitation, he needs two red sheets, five green sheets, and eight blue sheets. The store sells an infinite number of notebooks of each color, but each notebook consists of only one color with $$$k$$$ sheets. That is, each notebook contains $$$k$$$ sheets of either red, green, or blue.

Find the minimum number of notebooks that Petya needs to buy to invite all $$$n$$$ of his friends.

## File: /Users/mchiesa/work/projects/2026-02-dafny-liftings/dataset/0019_1080_A/task.dfy

```dafny
// A valid notebook purchase provides enough sheets of each color for n invitations.
// Each invitation requires 2 red, 5 green, and 8 blue sheets.
// Each notebook contains k sheets of a single color.
ghost predicate SufficientNotebooks(r: int, g: int, b: int, n: int, k: int)
{
  r >= 0 && g >= 0 && b >= 0 &&
  r * k >= 2 * n &&
  g * k >= 5 * n &&
  b * k >= 8 * n
}

// m is the minimum non-negative integer such that m * k >= need:
// the fewest k-sheet notebooks to obtain at least `need` sheets.
ghost predicate IsMinCover(m: int, need: int, k: int)
  requires k >= 1
{
  m >= 0 &&
  m * k >= need &&
  (m == 0 || (m - 1) * k < need)
}

// The minimum total notebooks for n invitations with k-sheet notebooks.
// Since colors are independent (notebooks are single-color), the global
// minimum equals the sum of per-color minima.
ghost predicate IsMinTotalNotebooks(total: int, n: int, k: int)
  requires n >= 1 && k >= 1
{
  exists r: nat ::
    exists g: nat ::
      exists b: nat ::
        IsMinCover(r, 2 * n, k) &&
        IsMinCover(g, 5 * n, k) &&
        IsMinCover(b, 8 * n, k) &&
        SufficientNotebooks(r, g, b, n, k) &&
        total == r + g + b
}

method PetyaAndOrigami(n: int, k: int) returns (notebooks: int)
  requires n >= 1 && k >= 1
  ensures IsMinTotalNotebooks(notebooks, n, k)
{
  notebooks := ((n * 2 + k - 1) / k) + ((n * 5 + k - 1) / k) + ((n * 8 + k - 1) / k);
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
   /opt/homebrew/Cellar/dotnet@8/8.0.124/libexec/dotnet /Users/mchiesa/work/projects/2026-02-dafny-liftings/dafny-source/Binaries/Dafny.dll verify /Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0019_1080_A/verified.dfy --verification-time-limit 60
   ```

5. If verification fails, read the error, fix the code, and retry.

6. Write the final result to `/Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0019_1080_A/verified.dfy`.
   Also write `/Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0019_1080_A/verify_result.json`:
   ```json
   {
     "verified": true/false,
     "attempts": N,
     "error": "last error if failed, null if verified"
   }
   ```

7. If you cannot verify after several attempts, save your best attempt as verified.dfy
   and set "verified": false in the result JSON.

IMPORTANT: Write output files to /Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0019_1080_A/ (create the directory if needed).

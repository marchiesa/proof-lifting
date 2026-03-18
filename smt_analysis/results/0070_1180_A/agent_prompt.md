Make this Dafny program verify. Add loop invariants, assertions, ghost variables,
and/or lemmas as needed. Do NOT modify the ghost spec (functions, predicates) or the method
signature (requires, ensures). Only add proof annotations inside method bodies.

## Problem: Alex and a Rhombus
While playing with geometric figures Alex has accidentally invented a concept of a $$$n$$$-th order rhombus in a cell grid.

A $$$1$$$-st order rhombus is just a square $$$1 \times 1$$$ (i.e just a cell).

A $$$n$$$-th order rhombus for all $$$n \geq 2$$$ one obtains from a $$$n-1$$$-th order rhombus adding all cells which have a common side with it to it (look at the picture to understand it better).

Alex asks you to compute the number of cells in a $$$n$$$-th order rhombus.

## File: /Users/mchiesa/work/projects/2026-02-dafny-liftings/dataset/0070_1180_A/task.dfy

```dafny
ghost function Abs(x: int): int
{
  if x >= 0 then x else -x
}

// A cell at grid position (x, y) belongs to the n-th order rhombus iff its
// Manhattan distance from the center (0, 0) is less than n. This characterizes
// the shape built by the problem's recursive construction: start with (0,0)
// and repeatedly adjoin all cells sharing a side.
ghost predicate InRhombus(x: int, y: int, n: int)
  requires n >= 1
{
  Abs(x) + Abs(y) <= n - 1
}

// For a given row x at radius r, count the integer y values with |x|+|y| <= r.
ghost function RowWidth(x: int, r: int): int
  requires r >= 0
{
  if Abs(x) > r then 0
  else 2 * (r - Abs(x)) + 1
}

// Sum RowWidth(x, r) for x in [lo .. hi].
ghost function SumRows(lo: int, hi: int, r: int): int
  requires r >= 0
  decreases if lo <= hi then hi - lo + 1 else 0
{
  if lo > hi then 0
  else RowWidth(lo, r) + SumRows(lo + 1, hi, r)
}

// Total cells in the n-th order rhombus: count of (x, y) with |x|+|y| <= n-1.
ghost function RhombusCellCount(n: int): int
  requires n >= 1
{
  SumRows(-(n - 1), n - 1, n - 1)
}

method Rhombus(n: int) returns (cells: int)
  requires n >= 1
  ensures cells == RhombusCellCount(n)
{
  cells := 1;
  var i := 1;
  while i < n
  {
    cells := cells + i * 4;
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
   /opt/homebrew/Cellar/dotnet@8/8.0.124/libexec/dotnet /Users/mchiesa/work/projects/2026-02-dafny-liftings/dafny-source/Binaries/Dafny.dll verify /Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0070_1180_A/verified.dfy --verification-time-limit 60
   ```

5. If verification fails, read the error, fix the code, and retry.

6. Write the final result to `/Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0070_1180_A/verified.dfy`.
   Also write `/Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0070_1180_A/verify_result.json`:
   ```json
   {
     "verified": true/false,
     "attempts": N,
     "error": "last error if failed, null if verified"
   }
   ```

7. If you cannot verify after several attempts, save your best attempt as verified.dfy
   and set "verified": false in the result JSON.

IMPORTANT: Write output files to /Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0070_1180_A/ (create the directory if needed).

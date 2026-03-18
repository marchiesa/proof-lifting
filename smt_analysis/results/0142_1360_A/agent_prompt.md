Make this Dafny program verify. Add loop invariants, assertions, ghost variables,
and/or lemmas as needed. Do NOT modify the ghost spec (functions, predicates) or the method
signature (requires, ensures). Only add proof annotations inside method bodies.

## Problem: Minimal Square
Find the minimum area of a square land on which you can place two identical rectangular $$$a \times b$$$ houses. The sides of the houses should be parallel to the sides of the desired square land.

Formally,

- You are given two identical rectangles with side lengths $$$a$$$ and $$$b$$$ ($$$1 \le a, b \le 100$$$) — positive integers (you are given just the sizes, but not their positions).
- Find the square of the minimum area that contains both given rectangles. Rectangles can be rotated (both or just one), moved, but the sides of the rectangles should be parallel to the sides of the desired square.

Two rectangles can touch each other (side or corner), but cannot intersect. Rectangles can also touch the sides of the square but must be completely inside it. You can rotate the rectangles. Take a look at the examples for a better understanding.

The picture shows a square that contains red and green rectangles.

## File: /Users/mchiesa/work/projects/2026-02-dafny-liftings/dataset/0142_1360_A/task.dfy

```dafny
// Two rectangles placed side by side (separated along x-axis) in a square of side s.
// Total width = w1 + w2; each height must fit within s.
ghost predicate FitsSideBySide(w1: int, h1: int, w2: int, h2: int, s: int)
{
  w1 + w2 <= s && h1 <= s && h2 <= s
}

// Two rectangles stacked (separated along y-axis) in a square of side s.
// Total height = h1 + h2; each width must fit within s.
ghost predicate FitsStacked(w1: int, h1: int, w2: int, h2: int, s: int)
{
  w1 <= s && w2 <= s && h1 + h2 <= s
}

// Whether two identical a×b rectangles (axis-parallel, possibly rotated) can be
// placed inside a square of side s without overlapping.
// By the separating axis theorem, non-overlapping axis-aligned rectangles are
// separated along at least one axis. We enumerate all orientation pairs
// {(a,b),(b,a)}^2 and both separation directions.
ghost predicate CanFitInSquare(a: int, b: int, s: int)
{
  FitsSideBySide(a, b, a, b, s) || FitsStacked(a, b, a, b, s) ||
  FitsSideBySide(a, b, b, a, s) || FitsStacked(a, b, b, a, s) ||
  FitsSideBySide(b, a, a, b, s) || FitsStacked(b, a, a, b, s) ||
  FitsSideBySide(b, a, b, a, s) || FitsStacked(b, a, b, a, s)
}

// s is the smallest square side length that can contain two a×b rectangles
ghost predicate IsMinimalSide(a: int, b: int, s: int)
{
  CanFitInSquare(a, b, s) && forall s' :: 1 <= s' < s ==> !CanFitInSquare(a, b, s')
}

method MinimalSquare(a: int, b: int) returns (area: int)
  requires 1 <= a && 1 <= b
  ensures exists s :: 1 <= s && area == s * s && IsMinimalSide(a, b, s)
{
  var lo := if a < b then a else b;
  var hi := if a < b then b else a;
  var val := if 2 * lo > hi then 2 * lo else hi;
  area := val * val;
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
   /opt/homebrew/Cellar/dotnet@8/8.0.124/libexec/dotnet /Users/mchiesa/work/projects/2026-02-dafny-liftings/dafny-source/Binaries/Dafny.dll verify /Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0142_1360_A/verified.dfy --verification-time-limit 60
   ```

5. If verification fails, read the error, fix the code, and retry.

6. Write the final result to `/Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0142_1360_A/verified.dfy`.
   Also write `/Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0142_1360_A/verify_result.json`:
   ```json
   {
     "verified": true/false,
     "attempts": N,
     "error": "last error if failed, null if verified"
   }
   ```

7. If you cannot verify after several attempts, save your best attempt as verified.dfy
   and set "verified": false in the result JSON.

IMPORTANT: Write output files to /Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0142_1360_A/ (create the directory if needed).

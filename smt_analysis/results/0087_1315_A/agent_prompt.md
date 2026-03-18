Make this Dafny program verify. Add loop invariants, assertions, ghost variables,
and/or lemmas as needed. Do NOT modify the ghost spec (functions, predicates) or the method
signature (requires, ensures). Only add proof annotations inside method bodies.

## Problem: Dead Pixel
Screen resolution of Polycarp's monitor is $$$a \times b$$$ pixels. Unfortunately, there is one dead pixel at his screen. It has coordinates $$$(x, y)$$$ ($$$0 \le x < a, 0 \le y < b$$$). You can consider columns of pixels to be numbered from $$$0$$$ to $$$a-1$$$, and rows — from $$$0$$$ to $$$b-1$$$.

Polycarp wants to open a rectangular window of maximal size, which doesn't contain the dead pixel. The boundaries of the window should be parallel to the sides of the screen.

Print the maximal area (in pixels) of a window that doesn't contain the dead pixel inside itself.

## File: /Users/mchiesa/work/projects/2026-02-dafny-liftings/dataset/0087_1315_A/task.dfy

```dafny
ghost predicate IsValidWindow(a: int, b: int, c1: int, r1: int, c2: int, r2: int)
{
  0 <= c1 <= c2 < a && 0 <= r1 <= r2 < b
}

ghost predicate WindowAvoidsDead(c1: int, r1: int, c2: int, r2: int, x: int, y: int)
{
  x < c1 || x > c2 || y < r1 || y > r2
}

ghost function WindowArea(c1: int, r1: int, c2: int, r2: int): int
{
  (c2 - c1 + 1) * (r2 - r1 + 1)
}

method DeadPixel(a: int, b: int, x: int, y: int) returns (area: int)
  requires a >= 1 && b >= 1
  requires 0 <= x < a && 0 <= y < b
  ensures area >= 0
  // Optimality: no valid window avoiding the dead pixel has area greater than the result
  ensures forall c1, r1, c2, r2 ::
    (0 <= c1 < a && 0 <= r1 < b && 0 <= c2 < a && 0 <= r2 < b &&
    IsValidWindow(a, b, c1, r1, c2, r2) && WindowAvoidsDead(c1, r1, c2, r2, x, y))
      ==> WindowArea(c1, r1, c2, r2) <= area
  // Achievability: the result is either 0 (no valid window) or achieved by some valid window
  ensures area == 0 ||
    (exists c1, r1, c2, r2 | 0 <= c1 < a && 0 <= r1 < b && 0 <= c2 < a && 0 <= r2 < b ::
      IsValidWindow(a, b, c1, r1, c2, r2) && WindowAvoidsDead(c1, r1, c2, r2, x, y) &&
      WindowArea(c1, r1, c2, r2) == area)
{
  var v1 := x * b;
  var v2 := y * a;
  var v3 := (a - x - 1) * b;
  var v4 := (b - y - 1) * a;
  area := v1;
  if v2 > area { area := v2; }
  if v3 > area { area := v3; }
  if v4 > area { area := v4; }
  return;
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
   /opt/homebrew/Cellar/dotnet@8/8.0.124/libexec/dotnet /Users/mchiesa/work/projects/2026-02-dafny-liftings/dafny-source/Binaries/Dafny.dll verify /Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0087_1315_A/verified.dfy --verification-time-limit 60
   ```

5. If verification fails, read the error, fix the code, and retry.

6. Write the final result to `/Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0087_1315_A/verified.dfy`.
   Also write `/Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0087_1315_A/verify_result.json`:
   ```json
   {
     "verified": true/false,
     "attempts": N,
     "error": "last error if failed, null if verified"
   }
   ```

7. If you cannot verify after several attempts, save your best attempt as verified.dfy
   and set "verified": false in the result JSON.

IMPORTANT: Write output files to /Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0087_1315_A/ (create the directory if needed).

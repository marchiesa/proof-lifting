Make this Dafny program verify. Add loop invariants, assertions, ghost variables,
and/or lemmas as needed. Do NOT modify the ghost spec (functions, predicates) or the method
signature (requires, ensures). Only add proof annotations inside method bodies.

## Problem: Four Segments
Monocarp wants to draw four line segments on a sheet of paper. He wants the $$$i$$$-th segment to have its length equal to $$$a_i$$$ ($$$1 \le i \le 4$$$). These segments can intersect with each other, and each segment should be either horizontal or vertical.

Monocarp wants to draw the segments in such a way that they enclose a rectangular space, and the area of that rectangular space should be maximum possible.

For example, if Monocarp wants to draw four segments with lengths $$$1$$$, $$$2$$$, $$$3$$$ and $$$4$$$, he can do it the following way:

Here, Monocarp has drawn segments $$$AB$$$ (with length $$$1$$$), $$$CD$$$ (with length $$$2$$$), $$$BC$$$ (with length $$$3$$$) and $$$EF$$$ (with length $$$4$$$). He got a rectangle $$$ABCF$$$ with area equal to $$$3$$$ that is enclosed by the segments.

Calculate the maximum area of a rectangle Monocarp can enclose with four segments.

## File: /Users/mchiesa/work/projects/2026-02-dafny-liftings/dataset/0177_1468_E/task.dfy

```dafny
// --- Specification ---

ghost function Min2(x: int, y: int): int {
  if x <= y then x else y
}

// Given that segments horizI and horizJ are the horizontal pair,
// returns the indices of the complementary (vertical) pair.
ghost function ComplementPair(horizI: int, horizJ: int): (int, int)
  requires 0 <= horizI < horizJ < 4
{
  if horizI == 0 && horizJ == 1 then (2, 3)
  else if horizI == 0 && horizJ == 2 then (1, 3)
  else if horizI == 0 && horizJ == 3 then (1, 2)
  else if horizI == 1 && horizJ == 2 then (0, 3)
  else if horizI == 1 && horizJ == 3 then (0, 2)
  else (0, 1)
}

// Rectangle width: limited by the shorter horizontal segment.
ghost function RectWidth(a: seq<int>, horizI: int, horizJ: int): int
  requires |a| == 4
  requires 0 <= horizI < horizJ < 4
{
  Min2(a[horizI], a[horizJ])
}

// Rectangle height: limited by the shorter vertical segment.
ghost function RectHeight(a: seq<int>, horizI: int, horizJ: int): int
  requires |a| == 4
  requires 0 <= horizI < horizJ < 4
{
  var vp := ComplementPair(horizI, horizJ);
  Min2(a[vp.0], a[vp.1])
}

// Area of the rectangle enclosed when segments horizI, horizJ are horizontal
// and the remaining two segments are vertical.
ghost function AssignmentArea(a: seq<int>, horizI: int, horizJ: int): int
  requires |a| == 4
  requires 0 <= horizI < horizJ < 4
{
  RectWidth(a, horizI, horizJ) * RectHeight(a, horizI, horizJ)
}

// True when 'area' is the maximum rectangle area over all ways to
// partition the four segments into a horizontal pair and a vertical pair.
ghost predicate IsOptimalArea(a: seq<int>, area: int)
  requires |a| == 4
{
  // Achievable: some assignment of 2 horizontal + 2 vertical yields this area
  (exists i | 0 <= i < 4 :: exists j | i + 1 <= j < 4 ::
    area == AssignmentArea(a, i, j))
  &&
  // Optimal: no assignment yields a larger area
  (forall i | 0 <= i < 4 :: forall j | i + 1 <= j < 4 ::
    area >= AssignmentArea(a, i, j))
}

// --- Implementation ---

method FourSegments(a: seq<int>) returns (area: int)
  requires |a| == 4
  requires forall i | 0 <= i < 4 :: a[i] > 0
  ensures IsOptimalArea(a, area)
{
  // Find max value and its index
  var maxVal := a[0];
  var maxIdx := 0;
  var i := 1;
  while i < |a|
  {
    if a[i] > maxVal {
      maxVal := a[i];
      maxIdx := i;
    }
    i := i + 1;
  }

  // Build remaining sequence without the first max
  var remaining: seq<int> := [];
  i := 0;
  while i < |a|
  {
    if i != maxIdx {
      remaining := remaining + [a[i]];
    }
    i := i + 1;
  }

  // Find min and max of remaining
  var lo := remaining[0];
  var hi := remaining[0];
  i := 1;
  while i < |remaining|
  {
    if remaining[i] < lo {
      lo := remaining[i];
    }
    if remaining[i] > hi {
      hi := remaining[i];
    }
    i := i + 1;
  }

  area := lo * hi;
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
   /opt/homebrew/Cellar/dotnet@8/8.0.124/libexec/dotnet /Users/mchiesa/work/projects/2026-02-dafny-liftings/dafny-source/Binaries/Dafny.dll verify /Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0177_1468_E/verified.dfy --verification-time-limit 60
   ```

5. If verification fails, read the error, fix the code, and retry.

6. Write the final result to `/Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0177_1468_E/verified.dfy`.
   Also write `/Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0177_1468_E/verify_result.json`:
   ```json
   {
     "verified": true/false,
     "attempts": N,
     "error": "last error if failed, null if verified"
   }
   ```

7. If you cannot verify after several attempts, save your best attempt as verified.dfy
   and set "verified": false in the result JSON.

IMPORTANT: Write output files to /Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0177_1468_E/ (create the directory if needed).

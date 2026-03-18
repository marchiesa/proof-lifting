Make this Dafny program verify. Add loop invariants, assertions, ghost variables,
and/or lemmas as needed. Do NOT modify the ghost spec (functions, predicates) or the method
signature (requires, ensures). Only add proof annotations inside method bodies.

## Problem: Letter
A boy Bob likes to draw. Not long ago he bought a rectangular graph (checked) sheet with n rows and m columns. Bob shaded some of the squares on the sheet. Having seen his masterpiece, he decided to share it with his elder brother, who lives in Flatland. Now Bob has to send his picture by post, but because of the world economic crisis and high oil prices, he wants to send his creation, but to spend as little money as possible. For each sent square of paper (no matter whether it is shaded or not) Bob has to pay 3.14 burles. Please, help Bob cut out of his masterpiece a rectangle of the minimum cost, that will contain all the shaded squares. The rectangle's sides should be parallel to the sheet's sides.

## File: /Users/mchiesa/work/projects/2026-02-dafny-liftings/dataset/0126_14_A/task.dfy

```dafny
// The grid has uniform row width (a rectangular sheet)
ghost predicate Rectangular(grid: seq<string>)
{
  |grid| > 0 &&
  forall i | 0 <= i < |grid| :: |grid[i]| == |grid[0]|
}

// The grid contains at least one shaded cell ('*')
ghost predicate HasStar(grid: seq<string>)
{
  exists r | 0 <= r < |grid| ::
    exists c | 0 <= c < |grid[r]| ::
      grid[r][c] == '*'
}

// The result is the sub-rectangle of grid spanning rows [top..bottom) and columns [left..right)
ghost predicate IsSubRectangle(grid: seq<string>, result: seq<string>,
                         top: int, bottom: int, left: int, right: int)
{
  0 <= top < bottom <= |grid| &&
  0 <= left < right &&
  (forall r | top <= r < bottom :: right <= |grid[r]|) &&
  |result| == bottom - top &&
  (forall i | 0 <= i < bottom - top :: result[i] == grid[top + i][left..right])
}

// Every shaded cell in the entire grid lies within the rectangle [top..bottom) x [left..right)
ghost predicate ContainsAllShaded(grid: seq<string>,
                            top: int, bottom: int, left: int, right: int)
{
  forall r | 0 <= r < |grid| ::
    forall c | 0 <= c < |grid[r]| ::
      grid[r][c] == '*' ==> (top <= r < bottom && left <= c < right)
}

// The rectangle is tight: each of its four edges touches at least one shaded cell.
// For axis-aligned rectangles, this is equivalent to having minimum area among all
// rectangles that contain every shaded cell.
ghost predicate TightBounds(grid: seq<string>,
                      top: int, bottom: int, left: int, right: int)
{
  0 <= top < bottom <= |grid| &&
  0 <= left < right &&
  (forall r | top <= r < bottom :: right <= |grid[r]|) &&
  // Top edge touches a shaded cell
  (exists c | left <= c < right :: grid[top][c] == '*') &&
  // Bottom edge touches a shaded cell
  (exists c | left <= c < right :: grid[bottom - 1][c] == '*') &&
  // Left edge touches a shaded cell
  (exists r | top <= r < bottom :: grid[r][left] == '*') &&
  // Right edge touches a shaded cell
  (exists r | top <= r < bottom :: grid[r][right - 1] == '*')
}

// The result is the minimum-cost rectangle cut from the grid containing all shaded cells
ghost predicate IsMinimalBoundingBox(grid: seq<string>, result: seq<string>,
                               top: int, bottom: int, left: int, right: int)
{
  IsSubRectangle(grid, result, top, bottom, left, right) &&
  ContainsAllShaded(grid, top, bottom, left, right) &&
  TightBounds(grid, top, bottom, left, right)
}

method Letter(grid: seq<string>) returns (result: seq<string>)
  decreases *
  requires Rectangular(grid)
  requires HasStar(grid)
  ensures exists top | 0 <= top < |grid| ::
            exists bottom | 0 <= bottom <= |grid| ::
              exists left | 0 <= left < |grid[0]| ::
                exists right | 0 <= right <= |grid[0]| ::
                  IsMinimalBoundingBox(grid, result, top, bottom, left, right)
{
  var lines := grid;

  while true
    decreases *
  {
    if |lines| == 0 { break; }

    // Check if any line starts with '*'
    var a := false;
    var i := 0;
    while i < |lines|
      decreases |lines| - i
    {
      if |lines[i]| > 0 && lines[i][0] == '*' {
        a := true;
        break;
      }
      i := i + 1;
    }
    if !a {
      var newLines: seq<string> := [];
      i := 0;
      while i < |lines|
        decreases |lines| - i
      {
        if |lines[i]| > 0 {
          newLines := newLines + [lines[i][1..]];
        }
        i := i + 1;
      }
      lines := newLines;
      continue;
    }

    // Check if any line ends with '*'
    var b := false;
    i := 0;
    while i < |lines|
      decreases |lines| - i
    {
      if |lines[i]| > 0 && lines[i][|lines[i]| - 1] == '*' {
        b := true;
        break;
      }
      i := i + 1;
    }
    if !b {
      var newLines: seq<string> := [];
      i := 0;
      while i < |lines|
        decreases |lines| - i
      {
        if |lines[i]| > 0 {
          newLines := newLines + [lines[i][..|lines[i]| - 1]];
        }
        i := i + 1;
      }
      lines := newLines;
      continue;
    }

    // Check if first row is all dots
    var allDots := true;
    var j := 0;
    while j < |lines[0]|
      decreases |lines[0]| - j
    {
      if lines[0][j] != '.' {
        allDots := false;
        break;
      }
      j := j + 1;
    }
    if allDots {
      lines := lines[1..];
      continue;
    }

    // Check if last row is all dots
    allDots := true;
    j := 0;
    while j < |lines[|lines| - 1]|
      decreases |lines[|lines| - 1]| - j
    {
      if lines[|lines| - 1][j] != '.' {
        allDots := false;
        break;
      }
      j := j + 1;
    }
    if allDots {
      lines := lines[..|lines| - 1];
      continue;
    }

    break;
  }

  result := lines;
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
   /opt/homebrew/Cellar/dotnet@8/8.0.124/libexec/dotnet /Users/mchiesa/work/projects/2026-02-dafny-liftings/dafny-source/Binaries/Dafny.dll verify /Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0126_14_A/verified.dfy --verification-time-limit 60
   ```

5. If verification fails, read the error, fix the code, and retry.

6. Write the final result to `/Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0126_14_A/verified.dfy`.
   Also write `/Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0126_14_A/verify_result.json`:
   ```json
   {
     "verified": true/false,
     "attempts": N,
     "error": "last error if failed, null if verified"
   }
   ```

7. If you cannot verify after several attempts, save your best attempt as verified.dfy
   and set "verified": false in the result JSON.

IMPORTANT: Write output files to /Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0126_14_A/ (create the directory if needed).

Make this Dafny program verify. Add loop invariants, assertions, ghost variables,
and/or lemmas as needed. Do NOT modify the ghost spec (functions, predicates) or the method
signature (requires, ensures). Only add proof annotations inside method bodies.

## Problem: Golden Plate
You have a plate and you want to add some gilding to it. The plate is a rectangle that we split into $$$w\times h$$$ cells. There should be $$$k$$$ gilded rings, the first one should go along the edge of the plate, the second one — $$$2$$$ cells away from the edge and so on. Each ring has a width of $$$1$$$ cell. Formally, the $$$i$$$-th of these rings should consist of all bordering cells on the inner rectangle of size $$$(w - 4(i - 1))\times(h - 4(i - 1))$$$.

The picture corresponds to the third example.

Your task is to compute the number of cells to be gilded.

## File: /Users/mchiesa/work/projects/2026-02-dafny-liftings/dataset/0002_1031_A/task.dfy

```dafny
ghost predicate OnBorder(r: int, c: int, top: int, left: int, rows: int, cols: int)
{
  rows >= 1 && cols >= 1 &&
  top <= r < top + rows && left <= c < left + cols &&
  (r == top || r == top + rows - 1 || c == left || c == left + cols - 1)
}

ghost predicate InRing(r: int, c: int, w: int, h: int, ring: int)
{
  OnBorder(r, c, 2 * ring, 2 * ring, h - 4 * ring, w - 4 * ring)
}

ghost predicate IsGilded(r: int, c: int, w: int, h: int, k: int)
{
  exists i | 0 <= i < k :: InRing(r, c, w, h, i)
}

ghost function CountGildedUpTo(w: int, h: int, k: int, n: int): int
  requires w >= 1 && h >= 1 && 0 <= n <= w * h
  decreases n
{
  if n == 0 then 0
  else
    var r := (n - 1) / w;
    var c := (n - 1) % w;
    CountGildedUpTo(w, h, k, n - 1) + (if IsGilded(r, c, w, h, k) then 1 else 0)
}

ghost function CountGilded(w: int, h: int, k: int): int
  requires w >= 1 && h >= 1
{
  CountGildedUpTo(w, h, k, w * h)
}

method {:verify false} GoldenPlate(w: int, h: int, k: int) returns (gilded: int)
  requires w >= 1 && h >= 1 && k >= 0
  ensures gilded == CountGilded(w, h, k)
{
  gilded := 0;
  var ww := w;
  var hh := h;
  var i := 0;
  while i < k
  {
    var minWH := if ww < hh then ww else hh;
    var maxWH := if ww > hh then ww else hh;
    if minWH == 1 {
      gilded := gilded + maxWH;
    } else {
      gilded := gilded + 2 * (ww + hh) - 4;
    }
    ww := ww - 4;
    hh := hh - 4;
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
   /opt/homebrew/Cellar/dotnet@8/8.0.124/libexec/dotnet /Users/mchiesa/work/projects/2026-02-dafny-liftings/dafny-source/Binaries/Dafny.dll verify /Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0002_1031_A/verified.dfy --verification-time-limit 60
   ```

5. If verification fails, read the error, fix the code, and retry.

6. Write the final result to `/Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0002_1031_A/verified.dfy`.
   Also write `/Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0002_1031_A/verify_result.json`:
   ```json
   {
     "verified": true/false,
     "attempts": N,
     "error": "last error if failed, null if verified"
   }
   ```

7. If you cannot verify after several attempts, save your best attempt as verified.dfy
   and set "verified": false in the result JSON.

IMPORTANT: Write output files to /Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0002_1031_A/ (create the directory if needed).

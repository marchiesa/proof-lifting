Make this Dafny program verify. Add loop invariants, assertions, ghost variables,
and/or lemmas as needed. Do NOT modify the ghost spec (functions, predicates) or the method
signature (requires, ensures). Only add proof annotations inside method bodies.

## Problem: Two Rival Students
You are the gym teacher in the school.

There are $$$n$$$ students in the row. And there are two rivalling students among them. The first one is in position $$$a$$$, the second in position $$$b$$$. Positions are numbered from $$$1$$$ to $$$n$$$ from left to right.

Since they are rivals, you want to maximize the distance between them. If students are in positions $$$p$$$ and $$$s$$$ respectively, then distance between them is $$$|p - s|$$$.

You can do the following operation at most $$$x$$$ times: choose two adjacent (neighbouring) students and swap them.

Calculate the maximum distance between two rivalling students after at most $$$x$$$ swaps.

## File: /Users/mchiesa/work/projects/2026-02-dafny-liftings/dataset/0085_1257_A/task.dfy

```dafny
// --- Specification ---

ghost function Abs(x: int): int
{
  if x >= 0 then x else -x
}

// Whether the relative order of two students flips from (a,b) to (pa,pb)
ghost predicate OrderFlipped(a: int, b: int, pa: int, pb: int)
{
  (a < b && pa > pb) || (a > b && pa < pb)
}

// Minimum adjacent swaps needed to move two specific students from positions
// (a, b) to positions (pa, pb) in a row. Each student requires |orig - target|
// swaps with intermediate neighbors. If their relative order must flip, one of
// those swaps is shared (they swap with each other), saving 1.
ghost function SwapCost(a: int, b: int, pa: int, pb: int): int
{
  Abs(a - pa) + Abs(b - pb) - (if OrderFlipped(a, b, pa, pb) then 1 else 0)
}

// There exist valid target positions that achieve exactly distance d
// using at most x adjacent swaps
ghost predicate IsAchievable(n: int, x: int, a: int, b: int, d: int)
  requires n >= 2 && 1 <= a <= n && 1 <= b <= n && a != b && x >= 0
{
  exists pa: int, pb: int | 1 <= pa <= n && 1 <= pb <= n ::
    pa != pb && Abs(pa - pb) == d && SwapCost(a, b, pa, pb) <= x
}

// d is the maximum distance achievable: it is achievable, and no reachable
// configuration yields a greater distance
ghost predicate IsMaxDistance(n: int, x: int, a: int, b: int, d: int)
  requires n >= 2 && 1 <= a <= n && 1 <= b <= n && a != b && x >= 0
{
  IsAchievable(n, x, a, b, d) &&
  forall pa: int, pb: int | 1 <= pa <= n && 1 <= pb <= n ::
    (pa != pb && SwapCost(a, b, pa, pb) <= x) ==> Abs(pa - pb) <= d
}

// --- Implementation ---

method TwoRivalStudents(n: int, x: int, a: int, b: int) returns (distance: int)
  requires n >= 2 && 1 <= a <= n && 1 <= b <= n && a != b && x >= 0
  ensures IsMaxDistance(n, x, a, b, distance)
{
  var la := a;
  var lb := b;
  var rx := x;
  if la > lb {
    var tmp := la;
    la := lb;
    lb := tmp;
  }
  var da := if la - 1 < rx then la - 1 else rx;
  la := la - da;
  rx := rx - da;
  var db := if n - lb < rx then n - lb else rx;
  lb := lb + db;
  distance := lb - la;
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
   /opt/homebrew/Cellar/dotnet@8/8.0.124/libexec/dotnet /Users/mchiesa/work/projects/2026-02-dafny-liftings/dafny-source/Binaries/Dafny.dll verify /Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0085_1257_A/verified.dfy --verification-time-limit 60
   ```

5. If verification fails, read the error, fix the code, and retry.

6. Write the final result to `/Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0085_1257_A/verified.dfy`.
   Also write `/Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0085_1257_A/verify_result.json`:
   ```json
   {
     "verified": true/false,
     "attempts": N,
     "error": "last error if failed, null if verified"
   }
   ```

7. If you cannot verify after several attempts, save your best attempt as verified.dfy
   and set "verified": false in the result JSON.

IMPORTANT: Write output files to /Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0085_1257_A/ (create the directory if needed).

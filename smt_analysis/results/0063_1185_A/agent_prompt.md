Make this Dafny program verify. Add loop invariants, assertions, ghost variables,
and/or lemmas as needed. Do NOT modify the ghost spec (functions, predicates) or the method
signature (requires, ensures). Only add proof annotations inside method bodies.

## Problem: Ropewalkers
Polycarp decided to relax on his weekend and visited to the performance of famous ropewalkers: Agafon, Boniface and Konrad.

The rope is straight and infinite in both directions. At the beginning of the performance, Agafon, Boniface and Konrad are located in positions $$$a$$$, $$$b$$$ and $$$c$$$ respectively. At the end of the performance, the distance between each pair of ropewalkers was at least $$$d$$$.

Ropewalkers can walk on the rope. In one second, only one ropewalker can change his position. Every ropewalker can change his position exactly by $$$1$$$ (i. e. shift by $$$1$$$ to the left or right direction on the rope). Agafon, Boniface and Konrad can not move at the same time (Only one of them can move at each moment). Ropewalkers can be at the same positions at the same time and can "walk past each other".

You should find the minimum duration (in seconds) of the performance. In other words, find the minimum number of seconds needed so that the distance between each pair of ropewalkers can be greater or equal to $$$d$$$.

Ropewalkers can walk to negative coordinates, due to the rope is infinite to both sides.

## File: /Users/mchiesa/work/projects/2026-02-dafny-liftings/dataset/0063_1185_A/task.dfy

```dafny
// ─────────────── Arithmetic helpers ───────────────

ghost function Abs(x: int): int {
  if x >= 0 then x else -x
}

ghost function Max(x: int, y: int): int {
  if x >= y then x else y
}

ghost function Min(x: int, y: int): int {
  if x <= y then x else y
}

// ─────────────── Sorting three values ───────────────

ghost function Min3(a: int, b: int, c: int): int {
  Min(a, Min(b, c))
}

ghost function Max3(a: int, b: int, c: int): int {
  Max(a, Max(b, c))
}

ghost function Mid3(a: int, b: int, c: int): int {
  a + b + c - Min3(a, b, c) - Max3(a, b, c)
}

// ─────────────── Problem-level predicates ───────────────

// A configuration of three walkers is valid iff every pair
// is separated by at least d.
ghost predicate AllPairsSeparated(p: int, q: int, r: int, d: int) {
  Abs(p - q) >= d && Abs(p - r) >= d && Abs(q - r) >= d
}

// Total unit moves for walkers to go from (a,b,c) to (a',b',c').
ghost function TotalMoves(a: int, b: int, c: int, a': int, b': int, c': int): int {
  Abs(a - a') + Abs(b - b') + Abs(c - c')
}

// ─────────────── Witness: optimal final positions ───────────────

// Keep the median walker fixed; push the lowest down and the
// highest up just enough to open gaps of at least d.
ghost function OptimalLo(a: int, b: int, c: int, d: int): int {
  Min(Min3(a, b, c), Mid3(a, b, c) - d)
}

ghost function OptimalMid(a: int, b: int, c: int, d: int): int {
  Mid3(a, b, c)
}

ghost function OptimalHi(a: int, b: int, c: int, d: int): int {
  Max(Max3(a, b, c), Mid3(a, b, c) + d)
}

// ─────────────── Minimum moves ───────────────

// The minimum total displacement is the sum of the gap deficits
// between consecutive sorted positions.
ghost function MinimumMoves(a: int, b: int, c: int, d: int): int {
  Max(0, d - (Mid3(a, b, c) - Min3(a, b, c)))
  + Max(0, d - (Max3(a, b, c) - Mid3(a, b, c)))
}

// ═══════════════════════════════════════════════════════

method Ropewalkers(a: int, b: int, c: int, d: int) returns (result: int)
  // The result equals the minimum total displacement
  ensures result == MinimumMoves(a, b, c, d)
  // The result is non-negative
  ensures result >= 0
  // Feasibility: the optimal final positions satisfy the separation constraint
  ensures AllPairsSeparated(OptimalLo(a, b, c, d), OptimalMid(a, b, c, d), OptimalHi(a, b, c, d), d)
  // The cost of reaching those optimal positions equals result
  ensures TotalMoves(Min3(a, b, c), Mid3(a, b, c), Max3(a, b, c),
                     OptimalLo(a, b, c, d), OptimalMid(a, b, c, d), OptimalHi(a, b, c, d)) == result
{
  var x := a;
  var y := b;
  var z := c;

  if x > y {
    var tmp := x;
    x := y;
    y := tmp;
  }
  if y > z {
    var tmp := y;
    y := z;
    z := tmp;
  }
  if x > y {
    var tmp := x;
    x := y;
    y := tmp;
  }

  var val1 := d - (y - x);
  var val2 := d - (z - y);
  if val1 < 0 { val1 := 0; }
  if val2 < 0 { val2 := 0; }

  result := val1 + val2;
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
   /opt/homebrew/Cellar/dotnet@8/8.0.124/libexec/dotnet /Users/mchiesa/work/projects/2026-02-dafny-liftings/dafny-source/Binaries/Dafny.dll verify /Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0063_1185_A/verified.dfy --verification-time-limit 60
   ```

5. If verification fails, read the error, fix the code, and retry.

6. Write the final result to `/Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0063_1185_A/verified.dfy`.
   Also write `/Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0063_1185_A/verify_result.json`:
   ```json
   {
     "verified": true/false,
     "attempts": N,
     "error": "last error if failed, null if verified"
   }
   ```

7. If you cannot verify after several attempts, save your best attempt as verified.dfy
   and set "verified": false in the result JSON.

IMPORTANT: Write output files to /Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0063_1185_A/ (create the directory if needed).

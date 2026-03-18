Make this Dafny program verify. Add loop invariants, assertions, ghost variables,
and/or lemmas as needed. Do NOT modify the ghost spec (functions, predicates) or the method
signature (requires, ensures). Only add proof annotations inside method bodies.

## Problem: Stones
Alice is playing with some stones.

Now there are three numbered heaps of stones. The first of them contains $$$a$$$ stones, the second of them contains $$$b$$$ stones and the third of them contains $$$c$$$ stones.

Each time she can do one of two operations:

1. take one stone from the first heap and two stones from the second heap (this operation can be done only if the first heap contains at least one stone and the second heap contains at least two stones);
2. take one stone from the second heap and two stones from the third heap (this operation can be done only if the second heap contains at least one stone and the third heap contains at least two stones).

She wants to get the maximum number of stones, but she doesn't know what to do. Initially, she has $$$0$$$ stones. Can you help her?

## File: /Users/mchiesa/work/projects/2026-02-dafny-liftings/dataset/0066_1236_A/task.dfy

```dafny
// A plan of x type-1 operations and y type-2 operations is feasible if the
// heaps have enough stones for a valid execution of those operations.
//
// Type-1 op: take 1 from heap a, 2 from heap b  (collects 3 stones)
// Type-2 op: take 1 from heap b, 2 from heap c  (collects 3 stones)
//
// The constraints below are necessary (each op draws from the heaps)
// and sufficient (executing all type-2 ops first, then all type-1 ops, is valid).
ghost predicate Feasible(a: int, b: int, c: int, x: int, y: int) {
  x >= 0 && y >= 0 && x <= a && 2 * x + y <= b && 2 * y <= c
}

ghost function StonesCollected(x: int, y: int): int {
  3 * (x + y)
}

method Stones(a: int, b: int, c: int) returns (maxStones: int)
  requires a >= 0 && b >= 0 && c >= 0
  // Achievability: some feasible plan yields exactly maxStones
  ensures exists x: int ::
            exists y: int ::
              Feasible(a, b, c, x, y) && maxStones == StonesCollected(x, y)
  // Optimality: no feasible plan yields more than maxStones
  ensures forall x: int ::
            forall y: int ::
              Feasible(a, b, c, x, y) ==> StonesCollected(x, y) <= maxStones
{
  var c2 := if c / 2 < b then c / 2 else b;
  var rem := if (b - c2) / 2 < a then (b - c2) / 2 else a;
  maxStones := (c2 + rem) * 3;
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
   /opt/homebrew/Cellar/dotnet@8/8.0.124/libexec/dotnet /Users/mchiesa/work/projects/2026-02-dafny-liftings/dafny-source/Binaries/Dafny.dll verify /Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0066_1236_A/verified.dfy --verification-time-limit 60
   ```

5. If verification fails, read the error, fix the code, and retry.

6. Write the final result to `/Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0066_1236_A/verified.dfy`.
   Also write `/Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0066_1236_A/verify_result.json`:
   ```json
   {
     "verified": true/false,
     "attempts": N,
     "error": "last error if failed, null if verified"
   }
   ```

7. If you cannot verify after several attempts, save your best attempt as verified.dfy
   and set "verified": false in the result JSON.

IMPORTANT: Write output files to /Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0066_1236_A/ (create the directory if needed).

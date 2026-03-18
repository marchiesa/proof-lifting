Make this Dafny program verify. Add loop invariants, assertions, ghost variables,
and/or lemmas as needed. Do NOT modify the ghost spec (functions, predicates) or the method
signature (requires, ensures). Only add proof annotations inside method bodies.

## Problem: Got Any Grapes?
For simplicity, we'll assume that there are only three types of grapes: green grapes, purple grapes and black grapes.

Andrew, Dmitry and Michal are all grapes' lovers, however their preferences of grapes are different. To make all of them happy, the following should happen:

- Andrew, Dmitry and Michal should eat at least $$$x$$$, $$$y$$$ and $$$z$$$ grapes, respectively.
- Andrew has an extreme affinity for green grapes, thus he will eat green grapes and green grapes only.
- On the other hand, Dmitry is not a fan of black grapes — any types of grapes except black would do for him. In other words, Dmitry can eat green and purple grapes.
- Michal has a common taste — he enjoys grapes in general and will be pleased with any types of grapes, as long as the quantity is sufficient.

Knowing that his friends are so fond of grapes, Aki decided to host a grape party with them. He has prepared a box with $$$a$$$ green grapes, $$$b$$$ purple grapes and $$$c$$$ black grapes.

However, Aki isn't sure if the box he prepared contains enough grapes to make everyone happy. Can you please find out whether it's possible to distribute grapes so that everyone is happy or Aki has to buy some more grapes?

It is not required to distribute all the grapes, so it's possible that some of them will remain unused.

## File: /Users/mchiesa/work/projects/2026-02-dafny-liftings/dataset/0065_1114_A/task.dfy

```dafny
// Checks whether a specific allocation of grapes satisfies all constraints:
//   ga/gd/gm = green grapes to Andrew/Dmitry/Michal
//   pd/pm    = purple grapes to Dmitry/Michal
//   bm       = black grapes to Michal
// Andrew eats only green; Dmitry eats green or purple; Michal eats any type.
ghost predicate ValidAllocation(x: int, y: int, z: int, a: int, b: int, c: int,
                          ga: int, gd: int, pd: int, gm: int, pm: int, bm: int)
{
  ga >= 0 && gd >= 0 && pd >= 0 && gm >= 0 && pm >= 0 && bm >= 0 &&
  ga >= x &&
  gd + pd >= y &&
  gm + pm + bm >= z &&
  ga + gd + gm <= a &&
  pd + pm <= b &&
  bm <= c
}

// There exists a distribution of grapes making everyone happy.
// We fix Andrew's share at exactly x green (giving more wastes green grapes).
// We search over gd: how many green grapes Dmitry receives.
// Dmitry's purple share is y - gd; Michal receives all remaining grapes.
ghost predicate Feasible(x: int, y: int, z: int, a: int, b: int, c: int)
  requires x >= 0 && y >= 0 && z >= 0 && a >= 0 && b >= 0 && c >= 0
{
  var bound := if a - x < y then a - x else y;
  exists gd: int | 0 <= gd <= bound ::
    ValidAllocation(x, y, z, a, b, c,
                    x, gd, y - gd, a - x - gd, b - (y - gd), c)
}

method GotAnyGrapes(x: int, y: int, z: int, a: int, b: int, c: int) returns (result: bool)
  requires x >= 0 && y >= 0 && z >= 0 && a >= 0 && b >= 0 && c >= 0
  ensures result == Feasible(x, y, z, a, b, c)
{
  var a' := a;
  var b' := b;
  var c' := c;

  c' := c' - z;
  if c' < 0 {
    b' := b' + c';
  }
  b' := b' - y;
  if b' < 0 {
    a' := a' + b';
  }
  a' := a' - x;

  result := a' >= 0;
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
   /opt/homebrew/Cellar/dotnet@8/8.0.124/libexec/dotnet /Users/mchiesa/work/projects/2026-02-dafny-liftings/dafny-source/Binaries/Dafny.dll verify /Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0065_1114_A/verified.dfy --verification-time-limit 60
   ```

5. If verification fails, read the error, fix the code, and retry.

6. Write the final result to `/Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0065_1114_A/verified.dfy`.
   Also write `/Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0065_1114_A/verify_result.json`:
   ```json
   {
     "verified": true/false,
     "attempts": N,
     "error": "last error if failed, null if verified"
   }
   ```

7. If you cannot verify after several attempts, save your best attempt as verified.dfy
   and set "verified": false in the result JSON.

IMPORTANT: Write output files to /Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0065_1114_A/ (create the directory if needed).

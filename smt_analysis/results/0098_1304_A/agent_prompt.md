Make this Dafny program verify. Add loop invariants, assertions, ghost variables,
and/or lemmas as needed. Do NOT modify the ghost spec (functions, predicates) or the method
signature (requires, ensures). Only add proof annotations inside method bodies.

## Problem: Two Rabbits
Being tired of participating in too many Codeforces rounds, Gildong decided to take some rest in a park. He sat down on a bench, and soon he found two rabbits hopping around. One of the rabbits was taller than the other.

He noticed that the two rabbits were hopping towards each other. The positions of the two rabbits can be represented as integer coordinates on a horizontal line. The taller rabbit is currently on position $$$x$$$, and the shorter rabbit is currently on position $$$y$$$ ($$$x \lt y$$$). Every second, each rabbit hops to another position. The taller rabbit hops to the positive direction by $$$a$$$, and the shorter rabbit hops to the negative direction by $$$b$$$.

For example, let's say $$$x=0$$$, $$$y=10$$$, $$$a=2$$$, and $$$b=3$$$. At the $$$1$$$-st second, each rabbit will be at position $$$2$$$ and $$$7$$$. At the $$$2$$$-nd second, both rabbits will be at position $$$4$$$.

Gildong is now wondering: Will the two rabbits be at the same position at the same moment? If so, how long will it take? Let's find a moment in time (in seconds) after which the rabbits will be at the same point.

## File: /Users/mchiesa/work/projects/2026-02-dafny-liftings/dataset/0098_1304_A/task.dfy

```dafny
ghost predicate MeetAt(x: int, y: int, a: int, b: int, t: int)
{
  t >= 1 && x + t * a == y - t * b
}

method TwoRabbits(x: int, y: int, a: int, b: int) returns (t: int)
  requires x < y
  requires a >= 1
  requires b >= 1
  ensures t == -1 || t >= 1
  ensures t >= 1 ==> MeetAt(x, y, a, b, t)
  ensures t == -1 ==> forall t' :: t' >= 1 ==> !MeetAt(x, y, a, b, t')
{
  var z := y - x;
  var c := a + b;
  if z % c != 0 {
    t := -1;
  } else {
    t := z / c;
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
   /opt/homebrew/Cellar/dotnet@8/8.0.124/libexec/dotnet /Users/mchiesa/work/projects/2026-02-dafny-liftings/dafny-source/Binaries/Dafny.dll verify /Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0098_1304_A/verified.dfy --verification-time-limit 60
   ```

5. If verification fails, read the error, fix the code, and retry.

6. Write the final result to `/Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0098_1304_A/verified.dfy`.
   Also write `/Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0098_1304_A/verify_result.json`:
   ```json
   {
     "verified": true/false,
     "attempts": N,
     "error": "last error if failed, null if verified"
   }
   ```

7. If you cannot verify after several attempts, save your best attempt as verified.dfy
   and set "verified": false in the result JSON.

IMPORTANT: Write output files to /Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0098_1304_A/ (create the directory if needed).

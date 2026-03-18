Make this Dafny program verify. Add loop invariants, assertions, ghost variables,
and/or lemmas as needed. Do NOT modify the ghost spec (functions, predicates) or the method
signature (requires, ensures). Only add proof annotations inside method bodies.

## Problem: Pens and Pencils
Tomorrow is a difficult day for Polycarp: he has to attend $$$a$$$ lectures and $$$b$$$ practical classes at the university! Since Polycarp is a diligent student, he is going to attend all of them.

While preparing for the university, Polycarp wonders whether he can take enough writing implements to write all of the lectures and draw everything he has to during all of the practical classes. Polycarp writes lectures using a pen (he can't use a pencil to write lectures!); he can write down $$$c$$$ lectures using one pen, and after that it runs out of ink. During practical classes Polycarp draws blueprints with a pencil (he can't use a pen to draw blueprints!); one pencil is enough to draw all blueprints during $$$d$$$ practical classes, after which it is unusable.

Polycarp's pencilcase can hold no more than $$$k$$$ writing implements, so if Polycarp wants to take $$$x$$$ pens and $$$y$$$ pencils, they will fit in the pencilcase if and only if $$$x + y \le k$$$.

Now Polycarp wants to know how many pens and pencils should he take. Help him to determine it, or tell that his pencilcase doesn't have enough room for all the implements he needs tomorrow!

Note that you don't have to minimize the number of writing implements (though their total number must not exceed $$$k$$$).

## File: /Users/mchiesa/work/projects/2026-02-dafny-liftings/dataset/0077_1244_A/task.dfy

```dafny
// A valid assignment: enough pens for all lectures, enough pencils for all
// practical classes, and they fit in the pencilcase.
ghost predicate ValidAssignment(x: int, y: int, a: int, b: int, c: int, d: int, k: int)
{
  x >= 0 && y >= 0 && x * c >= a && y * d >= b && x + y <= k
}

// The problem is feasible iff some valid assignment of pens and pencils exists.
ghost predicate Feasible(a: int, b: int, c: int, d: int, k: int)
{
  exists x :: exists y :: ValidAssignment(x, y, a, b, c, d, k)
}

method PensAndPencils(a: int, b: int, c: int, d: int, k: int) returns (x: int, y: int)
  requires a >= 1 && b >= 1 && c >= 1 && d >= 1 && k >= 1
  ensures Feasible(a, b, c, d, k) ==> ValidAssignment(x, y, a, b, c, d, k)
  ensures !Feasible(a, b, c, d, k) ==> x == -1
{
  var pens := (a + c - 1) / c;
  var pencils := (b + d - 1) / d;
  if pens + pencils <= k {
    return pens, pencils;
  } else {
    return -1, 0;
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
   /opt/homebrew/Cellar/dotnet@8/8.0.124/libexec/dotnet /Users/mchiesa/work/projects/2026-02-dafny-liftings/dafny-source/Binaries/Dafny.dll verify /Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0077_1244_A/verified.dfy --verification-time-limit 60
   ```

5. If verification fails, read the error, fix the code, and retry.

6. Write the final result to `/Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0077_1244_A/verified.dfy`.
   Also write `/Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0077_1244_A/verify_result.json`:
   ```json
   {
     "verified": true/false,
     "attempts": N,
     "error": "last error if failed, null if verified"
   }
   ```

7. If you cannot verify after several attempts, save your best attempt as verified.dfy
   and set "verified": false in the result JSON.

IMPORTANT: Write output files to /Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0077_1244_A/ (create the directory if needed).

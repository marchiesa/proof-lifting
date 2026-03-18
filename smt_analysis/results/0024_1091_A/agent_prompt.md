Make this Dafny program verify. Add loop invariants, assertions, ghost variables,
and/or lemmas as needed. Do NOT modify the ghost spec (functions, predicates) or the method
signature (requires, ensures). Only add proof annotations inside method bodies.

## Problem: New Year and the Christmas Ornament
Alice and Bob are decorating a Christmas Tree.

Alice wants only $$$3$$$ types of ornaments to be used on the Christmas Tree: yellow, blue and red. They have $$$y$$$ yellow ornaments, $$$b$$$ blue ornaments and $$$r$$$ red ornaments.

In Bob's opinion, a Christmas Tree will be beautiful if:

- the number of blue ornaments used is greater by exactly $$$1$$$ than the number of yellow ornaments, and
- the number of red ornaments used is greater by exactly $$$1$$$ than the number of blue ornaments.

That is, if they have $$$8$$$ yellow ornaments, $$$13$$$ blue ornaments and $$$9$$$ red ornaments, we can choose $$$4$$$ yellow, $$$5$$$ blue and $$$6$$$ red ornaments ($$$5=4+1$$$ and $$$6=5+1$$$).

Alice wants to choose as many ornaments as possible, but she also wants the Christmas Tree to be beautiful according to Bob's opinion.

In the example two paragraphs above, we would choose $$$7$$$ yellow, $$$8$$$ blue and $$$9$$$ red ornaments. If we do it, we will use $$$7+8+9=24$$$ ornaments. That is the maximum number.

Since Alice and Bob are busy with preparing food to the New Year's Eve, they are asking you to find out the maximum number of ornaments that can be used in their beautiful Christmas Tree!

It is guaranteed that it is possible to choose at least $$$6$$$ ($$$1+2+3=6$$$) ornaments.

## File: /Users/mchiesa/work/projects/2026-02-dafny-liftings/dataset/0024_1091_A/task.dfy

```dafny
ghost predicate Beautiful(ny: int, nb: int, nr: int)
{
  nb == ny + 1 && nr == nb + 1
}

ghost predicate ValidChoice(y: int, b: int, r: int, ny: int, nb: int, nr: int)
{
  0 <= ny <= y && 0 <= nb <= b && 0 <= nr <= r && Beautiful(ny, nb, nr)
}

method MaxOrnaments(y: int, b: int, r: int) returns (total: int)
  requires y >= 1 && b >= 2 && r >= 3
  ensures exists ny | 0 <= ny <= y ::
    ValidChoice(y, b, r, ny, ny + 1, ny + 2) &&
    total == ny + (ny + 1) + (ny + 2)
  ensures forall ny | 0 <= ny <= y ::
    ValidChoice(y, b, r, ny, ny + 1, ny + 2) ==>
    ny + (ny + 1) + (ny + 2) <= total
{
  var m := y;
  if b - 1 < m { m := b - 1; }
  if r - 2 < m { m := r - 2; }
  total := 3 * m + 3;
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
   /opt/homebrew/Cellar/dotnet@8/8.0.124/libexec/dotnet /Users/mchiesa/work/projects/2026-02-dafny-liftings/dafny-source/Binaries/Dafny.dll verify /Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0024_1091_A/verified.dfy --verification-time-limit 60
   ```

5. If verification fails, read the error, fix the code, and retry.

6. Write the final result to `/Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0024_1091_A/verified.dfy`.
   Also write `/Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0024_1091_A/verify_result.json`:
   ```json
   {
     "verified": true/false,
     "attempts": N,
     "error": "last error if failed, null if verified"
   }
   ```

7. If you cannot verify after several attempts, save your best attempt as verified.dfy
   and set "verified": false in the result JSON.

IMPORTANT: Write output files to /Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0024_1091_A/ (create the directory if needed).

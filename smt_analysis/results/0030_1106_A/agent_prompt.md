Make this Dafny program verify. Add loop invariants, assertions, ghost variables,
and/or lemmas as needed. Do NOT modify the ghost spec (functions, predicates) or the method
signature (requires, ensures). Only add proof annotations inside method bodies.

## Problem: Lunar New Year and Cross Counting
Lunar New Year is approaching, and you bought a matrix with lots of "crosses".

This matrix $$$M$$$ of size $$$n \times n$$$ contains only 'X' and '.' (without quotes). The element in the $$$i$$$-th row and the $$$j$$$-th column $$$(i, j)$$$ is defined as $$$M(i, j)$$$, where $$$1 \leq i, j \leq n$$$. We define a cross appearing in the $$$i$$$-th row and the $$$j$$$-th column ($$$1 < i, j < n$$$) if and only if $$$M(i, j) = M(i - 1, j - 1) = M(i - 1, j + 1) = M(i + 1, j - 1) = M(i + 1, j + 1) = $$$ 'X'.

The following figure illustrates a cross appearing at position $$$(2, 2)$$$ in a $$$3 \times 3$$$ matrix.

X.X.X.X.X

Your task is to find out the number of crosses in the given matrix $$$M$$$. Two crosses are different if and only if they appear in different rows or columns.

## File: /Users/mchiesa/work/projects/2026-02-dafny-liftings/dataset/0030_1106_A/task.dfy

```dafny
ghost predicate ValidMatrix(M: seq<seq<char>>, n: int)
{
  n >= 0 &&
  |M| == n &&
  (forall i | 0 <= i < n :: |M[i]| == n)
}

ghost predicate IsCrossAt(M: seq<seq<char>>, n: int, a: int, b: int)
  requires ValidMatrix(M, n)
  requires 0 <= a < n && 0 <= b < n
{
  1 <= a <= n - 2 &&
  1 <= b <= n - 2 &&
  M[a][b] == 'X' &&
  M[a-1][b-1] == 'X' &&
  M[a-1][b+1] == 'X' &&
  M[a+1][b-1] == 'X' &&
  M[a+1][b+1] == 'X'
}

ghost function CrossCount(M: seq<seq<char>>, n: int): int
  requires ValidMatrix(M, n)
{
  |set a, b | 0 <= a < n && 0 <= b < n && IsCrossAt(M, n, a, b) :: (a, b)|
}

method CountCrosses(n: int, M: seq<seq<char>>) returns (count: int)
  requires ValidMatrix(M, n)
  ensures count == CrossCount(M, n)
{
  count := 0;
  if n < 3 {
    return;
  }
  var a := 1;
  while a < n - 1
  {
    var b := 1;
    while b < n - 1
    {
      if M[a][b] == 'X'
         && M[a-1][b-1] == 'X'
         && M[a-1][b+1] == 'X'
         && M[a+1][b-1] == 'X'
         && M[a+1][b+1] == 'X'
      {
        count := count + 1;
      }
      b := b + 1;
    }
    a := a + 1;
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
   /opt/homebrew/Cellar/dotnet@8/8.0.124/libexec/dotnet /Users/mchiesa/work/projects/2026-02-dafny-liftings/dafny-source/Binaries/Dafny.dll verify /Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0030_1106_A/verified.dfy --verification-time-limit 60
   ```

5. If verification fails, read the error, fix the code, and retry.

6. Write the final result to `/Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0030_1106_A/verified.dfy`.
   Also write `/Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0030_1106_A/verify_result.json`:
   ```json
   {
     "verified": true/false,
     "attempts": N,
     "error": "last error if failed, null if verified"
   }
   ```

7. If you cannot verify after several attempts, save your best attempt as verified.dfy
   and set "verified": false in the result JSON.

IMPORTANT: Write output files to /Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0030_1106_A/ (create the directory if needed).

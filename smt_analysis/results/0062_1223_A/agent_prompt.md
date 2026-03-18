Make this Dafny program verify. Add loop invariants, assertions, ghost variables,
and/or lemmas as needed. Do NOT modify the ghost spec (functions, predicates) or the method
signature (requires, ensures). Only add proof annotations inside method bodies.

## Problem: CME
Let's denote correct match equation (we will denote it as CME) an equation $$$a + b = c$$$ there all integers $$$a$$$, $$$b$$$ and $$$c$$$ are greater than zero.

For example, equations $$$2 + 2 = 4$$$ (||+||=||||) and $$$1 + 2 = 3$$$ (|+||=|||) are CME but equations $$$1 + 2 = 4$$$ (|+||=||||), $$$2 + 2 = 3$$$ (||+||=|||), and $$$0 + 1 = 1$$$ (+|=|) are not.

Now, you have $$$n$$$ matches. You want to assemble a CME using all your matches. Unfortunately, it is possible that you can't assemble the CME using all matches. But you can buy some extra matches and then assemble CME!

For example, if $$$n = 2$$$, you can buy two matches and assemble |+|=||, and if $$$n = 5$$$ you can buy one match and assemble ||+|=|||.

Calculate the minimum number of matches which you have to buy for assembling CME.

Note, that you have to answer $$$q$$$ independent queries.

## File: /Users/mchiesa/work/projects/2026-02-dafny-liftings/dataset/0062_1223_A/task.dfy

```dafny
// A correct match equation (CME) is a + b = c where a, b, c are all positive integers
ghost predicate IsValidCME(a: int, b: int, c: int)
{
  a >= 1 && b >= 1 && c >= 1 && a + b == c
}

// Can exactly `total` matches be used to form a valid CME?
// Each of a, b, c is represented by that many matches, so a + b + c == total.
// Since c = a + b, we have a + b = total/2 and we search over valid values of a.
ghost predicate CanFormCMEWithMatches(total: int)
{
  exists a | 1 <= a <= total / 2 - 1 ::
    var b := total / 2 - a;
    IsValidCME(a, b, a + b) && a + b + (a + b) == total
}

method CME(n: int) returns (extra: int)
  ensures extra >= 0
  ensures CanFormCMEWithMatches(n + extra)
  ensures forall e | 0 <= e < extra :: !CanFormCMEWithMatches(n + e)
{
  if n < 4 {
    extra := 4 - n;
  } else {
    extra := n % 2;
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
   /opt/homebrew/Cellar/dotnet@8/8.0.124/libexec/dotnet /Users/mchiesa/work/projects/2026-02-dafny-liftings/dafny-source/Binaries/Dafny.dll verify /Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0062_1223_A/verified.dfy --verification-time-limit 60
   ```

5. If verification fails, read the error, fix the code, and retry.

6. Write the final result to `/Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0062_1223_A/verified.dfy`.
   Also write `/Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0062_1223_A/verify_result.json`:
   ```json
   {
     "verified": true/false,
     "attempts": N,
     "error": "last error if failed, null if verified"
   }
   ```

7. If you cannot verify after several attempts, save your best attempt as verified.dfy
   and set "verified": false in the result JSON.

IMPORTANT: Write output files to /Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0062_1223_A/ (create the directory if needed).

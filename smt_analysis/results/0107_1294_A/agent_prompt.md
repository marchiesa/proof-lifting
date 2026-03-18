Make this Dafny program verify. Add loop invariants, assertions, ghost variables,
and/or lemmas as needed. Do NOT modify the ghost spec (functions, predicates) or the method
signature (requires, ensures). Only add proof annotations inside method bodies.

## Problem: Collecting Coins
Polycarp has three sisters: Alice, Barbara, and Cerene. They're collecting coins. Currently, Alice has $$$a$$$ coins, Barbara has $$$b$$$ coins and Cerene has $$$c$$$ coins. Recently Polycarp has returned from the trip around the world and brought $$$n$$$ coins.

He wants to distribute all these $$$n$$$ coins between his sisters in such a way that the number of coins Alice has is equal to the number of coins Barbara has and is equal to the number of coins Cerene has. In other words, if Polycarp gives $$$A$$$ coins to Alice, $$$B$$$ coins to Barbara and $$$C$$$ coins to Cerene ($$$A+B+C=n$$$), then $$$a + A = b + B = c + C$$$.

Note that A, B or C (the number of coins Polycarp gives to Alice, Barbara and Cerene correspondingly) can be 0.

Your task is to find out if it is possible to distribute all $$$n$$$ coins between sisters in a way described above.

You have to answer $$$t$$$ independent test cases.

## File: /Users/mchiesa/work/projects/2026-02-dafny-liftings/dataset/0107_1294_A/task.dfy

```dafny
ghost predicate ValidDistribution(a: int, b: int, c: int, n: int, A: int, B: int, C: int)
{
  A >= 0 && B >= 0 && C >= 0
  && A + B + C == n
  && a + A == b + B
  && a + A == c + C
}

ghost predicate CanDistribute(a: int, b: int, c: int, n: int)
  requires n >= 0
{
  exists A: int, B: int, C: int
    :: ValidDistribution(a, b, c, n, A, B, C)
}

method CollectingCoins(a: int, b: int, c: int, n: int) returns (result: bool)
  requires a >= 0 && b >= 0 && c >= 0 && n >= 0
  ensures result == CanDistribute(a, b, c, n)
{
  var tot := a + b + c + n;
  if tot % 3 != 0 {
    return false;
  }
  var des := tot / 3;
  if a > des || b > des || c > des {
    return false;
  }
  return true;
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
   /opt/homebrew/Cellar/dotnet@8/8.0.124/libexec/dotnet /Users/mchiesa/work/projects/2026-02-dafny-liftings/dafny-source/Binaries/Dafny.dll verify /Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0107_1294_A/verified.dfy --verification-time-limit 60
   ```

5. If verification fails, read the error, fix the code, and retry.

6. Write the final result to `/Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0107_1294_A/verified.dfy`.
   Also write `/Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0107_1294_A/verify_result.json`:
   ```json
   {
     "verified": true/false,
     "attempts": N,
     "error": "last error if failed, null if verified"
   }
   ```

7. If you cannot verify after several attempts, save your best attempt as verified.dfy
   and set "verified": false in the result JSON.

IMPORTANT: Write output files to /Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0107_1294_A/ (create the directory if needed).

Make this Dafny program verify. Add loop invariants, assertions, ghost variables,
and/or lemmas as needed. Do NOT modify the ghost spec (functions, predicates) or the method
signature (requires, ensures). Only add proof annotations inside method bodies.

## Problem: Distinct Digits
You have two integers $$$l$$$ and $$$r$$$. Find an integer $$$x$$$ which satisfies the conditions below:

- $$$l \le x \le r$$$.
- All digits of $$$x$$$ are different.

If there are multiple answers, print any of them.

## File: /Users/mchiesa/work/projects/2026-02-dafny-liftings/dataset/0071_1228_A/task.dfy

```dafny
ghost function Digits(n: int): seq<int>
  requires n >= 0
  decreases n
{
  if n == 0 then []
  else Digits(n / 10) + [n % 10]
}

ghost predicate AllDistinct(s: seq<int>)
{
  forall i, j | 0 <= i < |s| && 0 <= j < |s| && i != j :: s[i] != s[j]
}

ghost predicate HasDistinctDigits(n: int)
  requires n >= 1
{
  AllDistinct(Digits(n))
}

method DistinctDigits(l: int, r: int) returns (x: int)
  requires l >= 1
  ensures x != -1 ==> l <= x <= r && HasDistinctDigits(x)
  ensures x == -1 ==> forall i | l <= i <= r :: !HasDistinctDigits(i)
{
  var i := l;
  while i <= r
  {
    var cnt := new int[10](_ => 0);
    var n := i;
    var ok := true;
    while n > 0
    {
      var d := n % 10;
      cnt[d] := cnt[d] + 1;
      if cnt[d] > 1 {
        ok := false;
      }
      n := n / 10;
    }
    if ok {
      return i;
    }
    i := i + 1;
  }
  return -1;
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
   /opt/homebrew/Cellar/dotnet@8/8.0.124/libexec/dotnet /Users/mchiesa/work/projects/2026-02-dafny-liftings/dafny-source/Binaries/Dafny.dll verify /Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0071_1228_A/verified.dfy --verification-time-limit 60
   ```

5. If verification fails, read the error, fix the code, and retry.

6. Write the final result to `/Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0071_1228_A/verified.dfy`.
   Also write `/Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0071_1228_A/verify_result.json`:
   ```json
   {
     "verified": true/false,
     "attempts": N,
     "error": "last error if failed, null if verified"
   }
   ```

7. If you cannot verify after several attempts, save your best attempt as verified.dfy
   and set "verified": false in the result JSON.

IMPORTANT: Write output files to /Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0071_1228_A/ (create the directory if needed).

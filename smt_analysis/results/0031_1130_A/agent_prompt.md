Make this Dafny program verify. Add loop invariants, assertions, ghost variables,
and/or lemmas as needed. Do NOT modify the ghost spec (functions, predicates) or the method
signature (requires, ensures). Only add proof annotations inside method bodies.

## Problem: Be Positive
You are given an array of $$$n$$$ integers: $$$a_1, a_2, \ldots, a_n$$$. Your task is to find some non-zero integer $$$d$$$ ($$$-10^3 \leq d \leq 10^3$$$) such that, after each number in the array is divided by $$$d$$$, the number of positive numbers that are presented in the array is greater than or equal to half of the array size (i.e., at least $$$\lceil\frac{n}{2}\rceil$$$). Note that those positive numbers do not need to be an integer (e.g., a $$$2.5$$$ counts as a positive number). If there are multiple values of $$$d$$$ that satisfy the condition, you may print any of them. In case that there is no such $$$d$$$, print a single integer $$$0$$$.

Recall that $$$\lceil x \rceil$$$ represents the smallest integer that is not less than $$$x$$$ and that zero ($$$0$$$) is neither positive nor negative.

## File: /Users/mchiesa/work/projects/2026-02-dafny-liftings/dataset/0031_1130_A/task.dfy

```dafny
ghost predicate IsPositiveAfterDiv(x: int, d: int)
  requires d != 0
{
  (x > 0 && d > 0) || (x < 0 && d < 0)
}

ghost function CountPositiveAfterDiv(a: seq<int>, d: int): int
  requires d != 0
  decreases |a|
{
  if |a| == 0 then 0
  else CountPositiveAfterDiv(a[..|a|-1], d)
       + (if IsPositiveAfterDiv(a[|a|-1], d) then 1 else 0)
}

ghost function CeilHalf(n: int): int
{
  (n + 1) / 2
}

method BePositive(a: seq<int>) returns (d: int)
  ensures d != 0 ==> -1000 <= d <= 1000
                      && CountPositiveAfterDiv(a, d) >= CeilHalf(|a|)
  ensures d == 0 ==> (forall d' :: d' == 0 || CountPositiveAfterDiv(a, d') < CeilHalf(|a|))
{
  var n := |a|;
  var pcount := 0;
  var ncount := 0;
  var zcount := 0;
  var i := 0;
  while i < n
  {
    if a[i] > 0 {
      pcount := pcount + 1;
    } else if a[i] < 0 {
      ncount := ncount + 1;
    } else {
      zcount := zcount + 1;
    }
    i := i + 1;
  }
  var half := (n + 1) / 2;
  if pcount >= half {
    d := 1;
  } else if ncount >= half {
    d := -1;
  } else {
    d := 0;
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
   /opt/homebrew/Cellar/dotnet@8/8.0.124/libexec/dotnet /Users/mchiesa/work/projects/2026-02-dafny-liftings/dafny-source/Binaries/Dafny.dll verify /Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0031_1130_A/verified.dfy --verification-time-limit 60
   ```

5. If verification fails, read the error, fix the code, and retry.

6. Write the final result to `/Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0031_1130_A/verified.dfy`.
   Also write `/Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0031_1130_A/verify_result.json`:
   ```json
   {
     "verified": true/false,
     "attempts": N,
     "error": "last error if failed, null if verified"
   }
   ```

7. If you cannot verify after several attempts, save your best attempt as verified.dfy
   and set "verified": false in the result JSON.

IMPORTANT: Write output files to /Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0031_1130_A/ (create the directory if needed).

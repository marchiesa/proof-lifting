Make this Dafny program verify. Add loop invariants, assertions, ghost variables,
and/or lemmas as needed. Do NOT modify the ghost spec (functions, predicates) or the method
signature (requires, ensures). Only add proof annotations inside method bodies.

## Problem: There Are Two Types Of Burgers
There are two types of burgers in your restaurant — hamburgers and chicken burgers! To assemble a hamburger you need two buns and a beef patty. To assemble a chicken burger you need two buns and a chicken cutlet.

You have $$$b$$$ buns, $$$p$$$ beef patties and $$$f$$$ chicken cutlets in your restaurant. You can sell one hamburger for $$$h$$$ dollars and one chicken burger for $$$c$$$ dollars. Calculate the maximum profit you can achieve.

You have to answer $$$t$$$ independent queries.

## File: /Users/mchiesa/work/projects/2026-02-dafny-liftings/dataset/0072_1207_A/task.dfy

```dafny
ghost predicate ValidAllocation(b: int, p: int, f: int, ham: int, chicken: int)
{
  ham >= 0 && chicken >= 0 &&
  ham <= p && chicken <= f &&
  2 * ham + 2 * chicken <= b
}

ghost function AllocationProfit(ham: int, chicken: int, h: int, c: int): int
{
  ham * h + chicken * c
}

ghost predicate IsMaxProfit(b: int, p: int, f: int, h: int, c: int, profit: int)
{
  (exists ham: int ::
    exists chicken: int ::
      ValidAllocation(b, p, f, ham, chicken) &&
      AllocationProfit(ham, chicken, h, c) == profit)
  &&
  (forall ham: int ::
    forall chicken: int ::
      !ValidAllocation(b, p, f, ham, chicken) ||
      AllocationProfit(ham, chicken, h, c) <= profit)
}

method MaxProfit(b: int, p: int, f: int, h: int, c: int) returns (profit: int)
  requires b >= 0 && p >= 0 && f >= 0 && h >= 0 && c >= 0
  ensures IsMaxProfit(b, p, f, h, c, profit)
{
  var lb := b;
  var lp := p;
  var lf := f;
  var lh := h;
  var lc := c;

  if lh < lc {
    var tmp := lh;
    lh := lc;
    lc := tmp;
    tmp := lp;
    lp := lf;
    lf := tmp;
  }

  var ham := lp;
  if lb / 2 < ham {
    ham := lb / 2;
  }
  profit := ham * lh;
  lb := lb - 2 * ham;

  var chicken := lf;
  if lb / 2 < chicken {
    chicken := lb / 2;
  }
  profit := profit + chicken * lc;
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
   /opt/homebrew/Cellar/dotnet@8/8.0.124/libexec/dotnet /Users/mchiesa/work/projects/2026-02-dafny-liftings/dafny-source/Binaries/Dafny.dll verify /Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0072_1207_A/verified.dfy --verification-time-limit 60
   ```

5. If verification fails, read the error, fix the code, and retry.

6. Write the final result to `/Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0072_1207_A/verified.dfy`.
   Also write `/Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0072_1207_A/verify_result.json`:
   ```json
   {
     "verified": true/false,
     "attempts": N,
     "error": "last error if failed, null if verified"
   }
   ```

7. If you cannot verify after several attempts, save your best attempt as verified.dfy
   and set "verified": false in the result JSON.

IMPORTANT: Write output files to /Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0072_1207_A/ (create the directory if needed).

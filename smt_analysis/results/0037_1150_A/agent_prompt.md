Make this Dafny program verify. Add loop invariants, assertions, ghost variables,
and/or lemmas as needed. Do NOT modify the ghost spec (functions, predicates) or the method
signature (requires, ensures). Only add proof annotations inside method bodies.

## Problem: Stock Arbitraging
Welcome to Codeforces Stock Exchange! We're pretty limited now as we currently allow trading on one stock, Codeforces Ltd. We hope you'll still be able to make profit from the market!

In the morning, there are $$$n$$$ opportunities to buy shares. The $$$i$$$-th of them allows to buy as many shares as you want, each at the price of $$$s_i$$$ bourles.

In the evening, there are $$$m$$$ opportunities to sell shares. The $$$i$$$-th of them allows to sell as many shares as you want, each at the price of $$$b_i$$$ bourles. You can't sell more shares than you have.

It's morning now and you possess $$$r$$$ bourles and no shares.

What is the maximum number of bourles you can hold after the evening?

## File: /Users/mchiesa/work/projects/2026-02-dafny-liftings/dataset/0037_1150_A/task.dfy

```dafny
ghost function Outcome(r: int, buyPrice: int, sellPrice: int, shares: int): int
{
  r - shares * buyPrice + shares * sellPrice
}

ghost predicate ValidTrade(r: int, buyPrice: int, shares: int)
{
  buyPrice > 0 && shares >= 0 && shares * buyPrice <= r
}

ghost predicate IsAchievable(result: int, r: int, s: seq<int>, b: seq<int>)
{
  result == r
  ||
  (exists i | 0 <= i < |s| :: exists j | 0 <= j < |b| :: exists k: nat ::
    ValidTrade(r, s[i], k) && result == Outcome(r, s[i], b[j], k))
}

ghost predicate IsOptimal(result: int, r: int, s: seq<int>, b: seq<int>)
{
  result >= r
  &&
  (forall i | 0 <= i < |s| :: forall j | 0 <= j < |b| :: forall k: nat ::
    ValidTrade(r, s[i], k) ==> Outcome(r, s[i], b[j], k) <= result)
}

method StockArbitraging(n: int, m: int, r: int, s: seq<int>, b: seq<int>) returns (maxBourles: int)
  requires |s| == n && n >= 1
  requires |b| == m && m >= 1
  requires r >= 1
  requires forall i | 0 <= i < n :: s[i] >= 1
  requires forall j | 0 <= j < m :: b[j] >= 1
  ensures IsAchievable(maxBourles, r, s, b)
  ensures IsOptimal(maxBourles, r, s, b)
{
  var minS := s[0];
  var i := 1;
  while i < |s|
  {
    if s[i] < minS {
      minS := s[i];
    }
    i := i + 1;
  }

  var maxB := b[0];
  i := 1;
  while i < |b|
  {
    if b[i] > maxB {
      maxB := b[i];
    }
    i := i + 1;
  }

  var profit := r % minS + (r / minS) * maxB;
  if profit > r {
    maxBourles := profit;
  } else {
    maxBourles := r;
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
   /opt/homebrew/Cellar/dotnet@8/8.0.124/libexec/dotnet /Users/mchiesa/work/projects/2026-02-dafny-liftings/dafny-source/Binaries/Dafny.dll verify /Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0037_1150_A/verified.dfy --verification-time-limit 60
   ```

5. If verification fails, read the error, fix the code, and retry.

6. Write the final result to `/Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0037_1150_A/verified.dfy`.
   Also write `/Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0037_1150_A/verify_result.json`:
   ```json
   {
     "verified": true/false,
     "attempts": N,
     "error": "last error if failed, null if verified"
   }
   ```

7. If you cannot verify after several attempts, save your best attempt as verified.dfy
   and set "verified": false in the result JSON.

IMPORTANT: Write output files to /Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0037_1150_A/ (create the directory if needed).

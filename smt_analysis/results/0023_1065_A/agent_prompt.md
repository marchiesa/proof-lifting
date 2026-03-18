Make this Dafny program verify. Add loop invariants, assertions, ghost variables,
and/or lemmas as needed. Do NOT modify the ghost spec (functions, predicates) or the method
signature (requires, ensures). Only add proof annotations inside method bodies.

## Problem: Vasya and Chocolate
There is a special offer in Vasya's favourite supermarket: if the customer buys $$$a$$$ chocolate bars, he or she may take $$$b$$$ additional bars for free. This special offer can be used any number of times.

Vasya currently has $$$s$$$ roubles, and he wants to get as many chocolate bars for free. Each chocolate bar costs $$$c$$$ roubles. Help Vasya to calculate the maximum possible number of chocolate bars he can get!

## File: /Users/mchiesa/work/projects/2026-02-dafny-liftings/dataset/0023_1065_A/task.dfy

```dafny
// Total chocolate bars when buying exactly `bought` bars under the
// "buy a, get b free" offer (usable any number of times).
// Each complete group of `a` purchased bars yields `b` free bars.
ghost function TotalChocolate(bought: int, a: int, b: int): int
  requires bought >= 0
  requires a > 0
{
  bought + (bought / a) * b
}

// Whether purchasing `bought` bars is affordable with budget `s` at price `c` each.
ghost predicate IsAffordable(bought: int, s: int, c: int)
  requires c > 0
{
  bought >= 0 && bought * c <= s
}

// The answer `ans` is the maximum total chocolate bars obtainable with budget `s`,
// bar price `c`, and the "buy `a` get `b` free" offer.
//
// Optimality argument: TotalChocolate is strictly non-decreasing in `bought`
// (each additional bar bought adds at least 1 to the total, since floor(n/a)
// is non-decreasing and b >= 0). Therefore the maximum total is achieved at
// the maximum affordable purchase.
ghost predicate IsMaxChocolateResult(s: int, a: int, b: int, c: int, ans: int)
  requires s >= 0 && a > 0 && b >= 0 && c > 0
{
  var bought := s / c;
  // (1) This purchase is affordable
  IsAffordable(bought, s, c)
  // (2) Cannot afford one more bar — bought is the maximum purchase
  && !IsAffordable(bought + 1, s, c)
  // (3) The answer equals the total bars from this maximum purchase
  && ans == TotalChocolate(bought, a, b)
  // (4) Non-decreasing at boundary: buying fewer gives no more total
  && (bought == 0 || TotalChocolate(bought, a, b) >= TotalChocolate(bought - 1, a, b))
}

method VasyaAndChocolate(t: int, cases: seq<(int, int, int, int)>) returns (results: seq<int>)
  requires t >= 0
  requires |cases| >= t
  requires forall i | 0 <= i < t ::
    cases[i].0 >= 0 && cases[i].1 > 0 && cases[i].2 >= 0 && cases[i].3 > 0
  ensures |results| == t
  ensures forall i | 0 <= i < t ::
    IsMaxChocolateResult(cases[i].0, cases[i].1, cases[i].2, cases[i].3, results[i])
{
  results := [];
  var i := 0;
  while i < t
  {
    var (s, a, b, c) := cases[i];
    var n := s / c;
    var x := n / a;
    var ans := n + x * b;
    results := results + [ans];
    i := i + 1;
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
   /opt/homebrew/Cellar/dotnet@8/8.0.124/libexec/dotnet /Users/mchiesa/work/projects/2026-02-dafny-liftings/dafny-source/Binaries/Dafny.dll verify /Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0023_1065_A/verified.dfy --verification-time-limit 60
   ```

5. If verification fails, read the error, fix the code, and retry.

6. Write the final result to `/Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0023_1065_A/verified.dfy`.
   Also write `/Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0023_1065_A/verify_result.json`:
   ```json
   {
     "verified": true/false,
     "attempts": N,
     "error": "last error if failed, null if verified"
   }
   ```

7. If you cannot verify after several attempts, save your best attempt as verified.dfy
   and set "verified": false in the result JSON.

IMPORTANT: Write output files to /Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0023_1065_A/ (create the directory if needed).

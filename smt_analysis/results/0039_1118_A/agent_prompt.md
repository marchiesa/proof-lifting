Make this Dafny program verify. Add loop invariants, assertions, ghost variables,
and/or lemmas as needed. Do NOT modify the ghost spec (functions, predicates) or the method
signature (requires, ensures). Only add proof annotations inside method bodies.

## Problem: Water Buying
Polycarp wants to cook a soup. To do it, he needs to buy exactly $$$n$$$ liters of water.

There are only two types of water bottles in the nearby shop — $$$1$$$-liter bottles and $$$2$$$-liter bottles. There are infinitely many bottles of these two types in the shop.

The bottle of the first type costs $$$a$$$ burles and the bottle of the second type costs $$$b$$$ burles correspondingly.

Polycarp wants to spend as few money as possible. Your task is to find the minimum amount of money (in burles) Polycarp needs to buy exactly $$$n$$$ liters of water in the nearby shop if the bottle of the first type costs $$$a$$$ burles and the bottle of the second type costs $$$b$$$ burles.

You also have to answer $$$q$$$ independent queries.

## File: /Users/mchiesa/work/projects/2026-02-dafny-liftings/dataset/0039_1118_A/task.dfy

```dafny
// --- Formal Specification ---

// A valid purchase of exactly n liters using 1-liter and 2-liter bottles
ghost predicate IsValidPurchase(ones: int, twos: int, n: int)
{
  ones >= 0 && twos >= 0 && ones + 2 * twos == n
}

// Total cost of purchasing ones 1-liter bottles at price a, twos 2-liter bottles at price b
ghost function PurchaseCost(ones: int, twos: int, a: int, b: int): int
{
  ones * a + twos * b
}

// The minimum cost to buy exactly n liters at prices a (per 1L) and b (per 2L).
// Any valid purchase is parameterized by twos in {0, ..., n/2} with ones = n - 2*twos.
// The total cost n*a + twos*(b - 2*a) is linear in twos, so the minimum
// over the integer interval [0, n/2] is at one of the two endpoints.
ghost function MinCost(n: int, a: int, b: int): int
  requires n >= 0
{
  var allOnesCost := PurchaseCost(n, 0, a, b);
  var maxTwosCost := PurchaseCost(n % 2, n / 2, a, b);
  if allOnesCost <= maxTwosCost then allOnesCost else maxTwosCost
}

// --- Implementation ---

method WaterBuying(queries: seq<(int, int, int)>) returns (results: seq<int>)
  requires forall i | 0 <= i < |queries| :: queries[i].0 >= 0
  ensures |results| == |queries|
  ensures forall i | 0 <= i < |queries| ::
    results[i] == MinCost(queries[i].0, queries[i].1, queries[i].2)
{
  results := [];
  var i := 0;
  while i < |queries|
  {
    var (n, a, b) := queries[i];
    var two := 2 * a;
    var m := if two < b then two else b;
    var ans := (n / 2) * m + (n % 2) * a;
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
   /opt/homebrew/Cellar/dotnet@8/8.0.124/libexec/dotnet /Users/mchiesa/work/projects/2026-02-dafny-liftings/dafny-source/Binaries/Dafny.dll verify /Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0039_1118_A/verified.dfy --verification-time-limit 60
   ```

5. If verification fails, read the error, fix the code, and retry.

6. Write the final result to `/Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0039_1118_A/verified.dfy`.
   Also write `/Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0039_1118_A/verify_result.json`:
   ```json
   {
     "verified": true/false,
     "attempts": N,
     "error": "last error if failed, null if verified"
   }
   ```

7. If you cannot verify after several attempts, save your best attempt as verified.dfy
   and set "verified": false in the result JSON.

IMPORTANT: Write output files to /Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0039_1118_A/ (create the directory if needed).

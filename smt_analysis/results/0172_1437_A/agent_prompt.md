Make this Dafny program verify. Add loop invariants, assertions, ghost variables,
and/or lemmas as needed. Do NOT modify the ghost spec (functions, predicates) or the method
signature (requires, ensures). Only add proof annotations inside method bodies.

## Problem: Marketing Scheme
You got a job as a marketer in a pet shop, and your current task is to boost sales of cat food. One of the strategies is to sell cans of food in packs with discounts.

Suppose you decided to sell packs with $$$a$$$ cans in a pack with a discount and some customer wants to buy $$$x$$$ cans of cat food. Then he follows a greedy strategy:

- he buys $$$\left\lfloor \frac{x}{a} \right\rfloor$$$ packs with a discount;
- then he wants to buy the remaining $$$(x \bmod a)$$$ cans one by one.

$$$\left\lfloor \frac{x}{a} \right\rfloor$$$ is $$$x$$$ divided by $$$a$$$ rounded down, $$$x \bmod a$$$ is the remainer of $$$x$$$ divided by $$$a$$$.

But customers are greedy in general, so if the customer wants to buy $$$(x \bmod a)$$$ cans one by one and it happens that $$$(x \bmod a) \ge \frac{a}{2}$$$ he decides to buy the whole pack of $$$a$$$ cans (instead of buying $$$(x \bmod a)$$$ cans). It makes you, as a marketer, happy since the customer bought more than he wanted initially.

You know that each of the customers that come to your shop can buy any number of cans from $$$l$$$ to $$$r$$$ inclusive. Can you choose such size of pack $$$a$$$ that each customer buys more cans than they wanted initially?

## File: /Users/mchiesa/work/projects/2026-02-dafny-liftings/dataset/0172_1437_A/task.dfy

```dafny
// Models the greedy customer behavior described in the problem:
// buy floor(x/a) packs, then if remainder >= a/2, buy one more full pack
ghost function CansActuallyBought(x: int, a: int): int
  requires a >= 1
{
  var packs := x / a;
  var remainder := x % a;
  if 2 * remainder >= a then
    (packs + 1) * a   // remainder >= a/2, so buys an extra full pack
  else
    packs * a + remainder  // buys remaining cans individually
}

// A customer wanting x cans ends up buying strictly more than x
ghost predicate CustomerBuysMore(x: int, a: int)
  requires a >= 1
{
  CansActuallyBought(x, a) > x
}

// Pack size a is valid: every customer wanting l..r cans buys more than wanted
ghost predicate AllCustomersBuyMore(l: int, r: int, a: int)
  requires l >= 1
  requires l <= r
  requires a >= 1
{
  forall x :: l <= x <= r ==> CustomerBuysMore(x, a)
}

// There exists a pack size making every customer in [l, r] buy more
// Bound: a > 2*r never works (x mod a = x, so 2*x <= 2*r < a, contradiction)
ghost predicate SchemeExists(l: int, r: int)
  requires l >= 1
  requires l <= r
{
  exists a :: a >= 1 && AllCustomersBuyMore(l, r, a)
}

method MarketingScheme(l: int, r: int) returns (result: bool)
  requires l >= 1
  requires l <= r
  ensures result == SchemeExists(l, r)
{
  result := l * 2 > r;
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
   /opt/homebrew/Cellar/dotnet@8/8.0.124/libexec/dotnet /Users/mchiesa/work/projects/2026-02-dafny-liftings/dafny-source/Binaries/Dafny.dll verify /Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0172_1437_A/verified.dfy --verification-time-limit 60
   ```

5. If verification fails, read the error, fix the code, and retry.

6. Write the final result to `/Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0172_1437_A/verified.dfy`.
   Also write `/Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0172_1437_A/verify_result.json`:
   ```json
   {
     "verified": true/false,
     "attempts": N,
     "error": "last error if failed, null if verified"
   }
   ```

7. If you cannot verify after several attempts, save your best attempt as verified.dfy
   and set "verified": false in the result JSON.

IMPORTANT: Write output files to /Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0172_1437_A/ (create the directory if needed).

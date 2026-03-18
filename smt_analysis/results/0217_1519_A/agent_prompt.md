Make this Dafny program verify. Add loop invariants, assertions, ghost variables,
and/or lemmas as needed. Do NOT modify the ghost spec (functions, predicates) or the method
signature (requires, ensures). Only add proof annotations inside method bodies.

## Problem: Red and Blue Beans
You have $$$r$$$ red and $$$b$$$ blue beans. You'd like to distribute them among several (maybe, one) packets in such a way that each packet:

- has at least one red bean (or the number of red beans $$$r_i \ge 1$$$);
- has at least one blue bean (or the number of blue beans $$$b_i \ge 1$$$);
- the number of red and blue beans should differ in no more than $$$d$$$ (or $$$|r_i - b_i| \le d$$$)

Can you distribute all beans?

## File: /Users/mchiesa/work/projects/2026-02-dafny-liftings/dataset/0217_1519_A/task.dfy

```dafny
ghost function Abs(x: int): int {
  if x >= 0 then x else -x
}

ghost function Min(a: int, b: int): int {
  if a <= b then a else b
}

// A single packet is valid if it has >=1 of each color and the counts differ by at most d.
ghost predicate ValidPacket(ri: int, bi: int, d: int) {
  ri >= 1 && bi >= 1 && Abs(ri - bi) <= d
}

// Can we distribute exactly r red and b blue beans into exactly n valid packets?
// We choose how many red (ri) and blue (bi) beans go in the first packet,
// then recursively distribute the rest into n-1 packets.
ghost predicate CanDistributeInN(r: int, b: int, d: int, n: nat)
  decreases n
{
  if n == 0 then
    r == 0 && b == 0
  else if r < n || b < n then
    false  // not enough beans for each remaining packet to get at least 1
  else if n == 1 then
    ValidPacket(r, b, d)
  else
    exists ri | 1 <= ri <= r - (n - 1) ::
      exists bi | 1 <= bi <= b - (n - 1) ::
        ValidPacket(ri, bi, d) &&
        CanDistributeInN(r - ri, b - bi, d, n - 1)
}

// Can we distribute r red and b blue beans into some number of valid packets?
ghost predicate CanDistribute(r: int, b: int, d: int) {
  exists n | 1 <= n <= Min(r, b) :: CanDistributeInN(r, b, d, n)
}

method RedAndBlueBeans(r: int, b: int, d: int) returns (result: bool)
  requires r >= 1 && b >= 1 && d >= 0
  ensures result == CanDistribute(r, b, d)
{
  var rr := r;
  var bb := b;
  if rr > bb {
    var tmp := rr;
    rr := bb;
    bb := tmp;
  }
  result := rr * (d + 1) >= bb;
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
   /opt/homebrew/Cellar/dotnet@8/8.0.124/libexec/dotnet /Users/mchiesa/work/projects/2026-02-dafny-liftings/dafny-source/Binaries/Dafny.dll verify /Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0217_1519_A/verified.dfy --verification-time-limit 60
   ```

5. If verification fails, read the error, fix the code, and retry.

6. Write the final result to `/Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0217_1519_A/verified.dfy`.
   Also write `/Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0217_1519_A/verify_result.json`:
   ```json
   {
     "verified": true/false,
     "attempts": N,
     "error": "last error if failed, null if verified"
   }
   ```

7. If you cannot verify after several attempts, save your best attempt as verified.dfy
   and set "verified": false in the result JSON.

IMPORTANT: Write output files to /Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0217_1519_A/ (create the directory if needed).

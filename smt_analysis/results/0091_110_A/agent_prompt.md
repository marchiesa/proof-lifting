Make this Dafny program verify. Add loop invariants, assertions, ghost variables,
and/or lemmas as needed. Do NOT modify the ghost spec (functions, predicates) or the method
signature (requires, ensures). Only add proof annotations inside method bodies.

## Problem: Nearly Lucky Number
Petya loves lucky numbers. We all know that lucky numbers are the positive integers whose decimal representations contain only the lucky digits 4 and 7. For example, numbers 47, 744, 4 are lucky and 5, 17, 467 are not.

Unfortunately, not all numbers are lucky. Petya calls a number nearly lucky if the number of lucky digits in it is a lucky number. He wonders whether number n is a nearly lucky number.

## File: /Users/mchiesa/work/projects/2026-02-dafny-liftings/dataset/0091_110_A/task.dfy

```dafny
// --- Specification ---

ghost function Abs(n: int): nat {
  if n < 0 then -n else n
}

ghost predicate IsLuckyDigit(d: int) {
  d == 4 || d == 7
}

// Decimal digits of a positive number (most-significant first); 0 maps to [].
ghost function Digits(n: nat): seq<int>
  decreases n
{
  if n == 0 then []
  else Digits(n / 10) + [n % 10]
}

// Count of lucky digits in a sequence (slice-based recursion).
ghost function CountLucky(s: seq<int>): nat
  decreases |s|
{
  if |s| == 0 then 0
  else CountLucky(s[..|s|-1]) + (if IsLuckyDigit(s[|s|-1]) then 1 else 0)
}

// A lucky number is a positive integer whose every digit is 4 or 7.
ghost predicate IsLuckyNumber(n: nat) {
  var d := Digits(n);
  n > 0 && forall i :: 0 <= i < |d| ==> IsLuckyDigit(d[i])
}

// A number is nearly lucky iff the count of lucky digits in its
// decimal representation is itself a lucky number.
ghost predicate IsNearlyLucky(n: int) {
  IsLuckyNumber(CountLucky(Digits(Abs(n))))
}

// --- Implementation (body unchanged) ---

method NearlyLucky(n: int) returns (result: bool)
  ensures result == IsNearlyLucky(n)
{
  var num := if n < 0 then -n else n;
  if num == 0 {
    result := false;
    return;
  }
  var count := 0;
  var temp := num;
  while temp > 0 {
    var digit := temp % 10;
    if digit == 4 || digit == 7 {
      count := count + 1;
    }
    temp := temp / 10;
  }
  if count == 0 {
    result := false;
    return;
  }
  var flag := true;
  temp := count;
  while temp > 0 {
    var digit := temp % 10;
    if digit != 4 && digit != 7 {
      flag := false;
    }
    temp := temp / 10;
  }
  result := flag;
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
   /opt/homebrew/Cellar/dotnet@8/8.0.124/libexec/dotnet /Users/mchiesa/work/projects/2026-02-dafny-liftings/dafny-source/Binaries/Dafny.dll verify /Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0091_110_A/verified.dfy --verification-time-limit 60
   ```

5. If verification fails, read the error, fix the code, and retry.

6. Write the final result to `/Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0091_110_A/verified.dfy`.
   Also write `/Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0091_110_A/verify_result.json`:
   ```json
   {
     "verified": true/false,
     "attempts": N,
     "error": "last error if failed, null if verified"
   }
   ```

7. If you cannot verify after several attempts, save your best attempt as verified.dfy
   and set "verified": false in the result JSON.

IMPORTANT: Write output files to /Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0091_110_A/ (create the directory if needed).

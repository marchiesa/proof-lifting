Make this Dafny program verify. Add loop invariants, assertions, ghost variables,
and/or lemmas as needed. Do NOT modify the ghost spec (functions, predicates) or the method
signature (requires, ensures). Only add proof annotations inside method bodies.

## Problem: Strange Functions
Let's define a function $$$f(x)$$$ ($$$x$$$ is a positive integer) as follows: write all digits of the decimal representation of $$$x$$$ backwards, then get rid of the leading zeroes. For example, $$$f(321) = 123$$$, $$$f(120) = 21$$$, $$$f(1000000) = 1$$$, $$$f(111) = 111$$$.

Let's define another function $$$g(x) = \dfrac{x}{f(f(x))}$$$ ($$$x$$$ is a positive integer as well).

Your task is the following: for the given positive integer $$$n$$$, calculate the number of different values of $$$g(x)$$$ among all numbers $$$x$$$ such that $$$1 \le x \le n$$$.

## File: /Users/mchiesa/work/projects/2026-02-dafny-liftings/dataset/0178_1455_A/task.dfy

```dafny
// --- Specification: models the problem's operations directly ---

// Convert a digit sequence (most-significant first) to its numeric value
ghost function DigitsToNat(s: seq<int>): int
  decreases |s|
{
  if |s| == 0 then 0
  else DigitsToNat(s[..|s|-1]) * 10 + s[|s|-1]
}

// Convert a non-negative integer to its digit sequence
ghost function NatToDigits(n: int): seq<int>
  decreases n
{
  if n < 0 then [0]
  else if n < 10 then [n]
  else NatToDigits(n / 10) + [n % 10]
}

// Reverse a sequence
ghost function ReverseSeq(s: seq<int>): seq<int>
  decreases |s|
{
  if |s| == 0 then []
  else [s[|s|-1]] + ReverseSeq(s[..|s|-1])
}

// Strip leading zeros, keeping at least one digit
ghost function StripLeadingZeros(s: seq<int>): seq<int>
  decreases |s|
{
  if |s| <= 1 then s
  else if s[0] == 0 then StripLeadingZeros(s[1..])
  else s
}

// f(x): write all digits of x backwards, then strip leading zeros
ghost function ReverseDigits(x: int): int
{
  if x < 0 then 0
  else
    var digits := NatToDigits(x);
    var reversed := ReverseSeq(digits);
    var stripped := StripLeadingZeros(reversed);
    DigitsToNat(stripped)
}

// g(x) = x / f(f(x))
ghost function GValue(x: int): int
{
  if x < 1 then 0
  else
    var ffx := ReverseDigits(ReverseDigits(x));
    if ffx == 0 then 0
    else x / ffx
}

// The number of distinct g(x) values for 1 <= x <= N
ghost function CountDistinctGValues(N: int): int
{
  if N < 1 then 0
  else |set x: int | 1 <= x <= N :: GValue(x)|
}

// A valid representation of a positive integer as a digit sequence
ghost predicate ValidPositiveDigitSeq(s: seq<int>)
{
  |s| > 0 &&
  s[0] != 0 &&
  (forall i | 0 <= i < |s| :: 0 <= s[i] <= 9)
}

// --- Working code with specification attached ---

method StrangeFunctions(n: seq<int>) returns (result: int)
  requires ValidPositiveDigitSeq(n)
  ensures result == CountDistinctGValues(DigitsToNat(n))
{
  result := |n|;
}

method Repeat(d: int, count: int) returns (s: seq<int>)
{
  s := [];
  var i := 0;
  while i < count {
    s := s + [d];
    i := i + 1;
  }
}

method StringToDigits(str: string) returns (s: seq<int>)
{
  s := [];
  var i := 0;
  while i < |str| {
    s := s + [str[i] as int - '0' as int];
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
   /opt/homebrew/Cellar/dotnet@8/8.0.124/libexec/dotnet /Users/mchiesa/work/projects/2026-02-dafny-liftings/dafny-source/Binaries/Dafny.dll verify /Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0178_1455_A/verified.dfy --verification-time-limit 60
   ```

5. If verification fails, read the error, fix the code, and retry.

6. Write the final result to `/Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0178_1455_A/verified.dfy`.
   Also write `/Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0178_1455_A/verify_result.json`:
   ```json
   {
     "verified": true/false,
     "attempts": N,
     "error": "last error if failed, null if verified"
   }
   ```

7. If you cannot verify after several attempts, save your best attempt as verified.dfy
   and set "verified": false in the result JSON.

IMPORTANT: Write output files to /Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0178_1455_A/ (create the directory if needed).

Make this Dafny program verify. Add loop invariants, assertions, ghost variables,
and/or lemmas as needed. Do NOT modify the ghost spec (functions, predicates) or the method
signature (requires, ensures). Only add proof annotations inside method bodies.

## Problem: Telephone Number
A telephone number is a sequence of exactly 11 digits, where the first digit is 8. For example, the sequence 80011223388 is a telephone number, but the sequences 70011223388 and 80000011223388 are not.

You are given a string $$$s$$$ of length $$$n$$$, consisting of digits.

In one operation you can delete any character from string $$$s$$$. For example, it is possible to obtain strings 112, 111 or 121 from string 1121.

You need to determine whether there is such a sequence of operations (possibly empty), after which the string $$$s$$$ becomes a telephone number.

## File: /Users/mchiesa/work/projects/2026-02-dafny-liftings/dataset/0059_1167_A/task.dfy

```dafny
// --- Formal specification predicates ---

ghost predicate IsDigit(c: char)
{
  '0' <= c <= '9'
}

// A telephone number is exactly 11 digits where the first digit is '8'.
ghost predicate IsPhoneNumber(t: seq<char>)
{
  |t| == 11 && t[0] == '8' && (forall i | 0 <= i < |t| :: IsDigit(t[i]))
}

// `sub` can be obtained from `s` by deleting zero or more characters (preserving order).
ghost predicate IsSubsequence(sub: seq<char>, s: seq<char>)
  decreases |s|
{
  if |sub| == 0 then true
  else if |s| == 0 then false
  else
    // Either match sub[0] with s[0] and advance both, or skip s[0]
    (sub[0] == s[0] && IsSubsequence(sub[1..], s[1..]))
    || IsSubsequence(sub, s[1..])
}

// Compilable equivalent of: exists t :: IsPhoneNumber(t) && IsSubsequence(t, s).
// Enumerates all ways to select `remaining` characters from s in order;
// the first selected character must be '8', and every selected character must be a digit.
ghost predicate CanFormPhone(s: seq<char>, remaining: nat)
  decreases |s|
{
  if remaining == 0 then true
  else if |s| == 0 then false
  else
    // Skip s[0]
    CanFormPhone(s[1..], remaining)
    ||
    // Select s[0] as the next phone-number digit
    (IsDigit(s[0]) && (remaining == 11 ==> s[0] == '8') && CanFormPhone(s[1..], remaining - 1))
}

// --- Method with specification ---

method TelephoneNumber(s: string, n: int) returns (result: bool)
  requires n == |s|
  requires forall i | 0 <= i < n :: IsDigit(s[i])
  ensures result == CanFormPhone(s, 11)
{
  var i := 0;
  while i < n - 10
  {
    if s[i] == '8' {
      return true;
    }
    i := i + 1;
  }
  return false;
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
   /opt/homebrew/Cellar/dotnet@8/8.0.124/libexec/dotnet /Users/mchiesa/work/projects/2026-02-dafny-liftings/dafny-source/Binaries/Dafny.dll verify /Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0059_1167_A/verified.dfy --verification-time-limit 60
   ```

5. If verification fails, read the error, fix the code, and retry.

6. Write the final result to `/Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0059_1167_A/verified.dfy`.
   Also write `/Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0059_1167_A/verify_result.json`:
   ```json
   {
     "verified": true/false,
     "attempts": N,
     "error": "last error if failed, null if verified"
   }
   ```

7. If you cannot verify after several attempts, save your best attempt as verified.dfy
   and set "verified": false in the result JSON.

IMPORTANT: Write output files to /Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0059_1167_A/ (create the directory if needed).

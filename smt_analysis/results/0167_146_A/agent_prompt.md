Make this Dafny program verify. Add loop invariants, assertions, ghost variables,
and/or lemmas as needed. Do NOT modify the ghost spec (functions, predicates) or the method
signature (requires, ensures). Only add proof annotations inside method bodies.

## Problem: Lucky Ticket
Petya loves lucky numbers very much. Everybody knows that lucky numbers are positive integers whose decimal record contains only the lucky digits 4 and 7. For example, numbers 47, 744, 4 are lucky and 5, 17, 467 are not.

Petya loves tickets very much. As we know, each ticket has a number that is a positive integer. Its length equals n (n is always even). Petya calls a ticket lucky if the ticket's number is a lucky number and the sum of digits in the first half (the sum of the first n / 2 digits) equals the sum of digits in the second half (the sum of the last n / 2 digits). Check if the given ticket is lucky.

## File: /Users/mchiesa/work/projects/2026-02-dafny-liftings/dataset/0167_146_A/task.dfy

```dafny
ghost predicate IsLuckyDigit(c: char)
{
  c == '4' || c == '7'
}

ghost predicate AllLuckyDigits(s: seq<char>)
{
  forall i | 0 <= i < |s| :: IsLuckyDigit(s[i])
}

ghost function DigitValue(c: char): int
{
  (c as int) - ('0' as int)
}

ghost function DigitSum(s: seq<char>): int
  decreases |s|
{
  if |s| == 0 then 0
  else DigitSum(s[..|s|-1]) + DigitValue(s[|s|-1])
}

ghost predicate IsLuckyTicket(s: seq<char>)
{
  var half := |s| / 2;
  AllLuckyDigits(s) && DigitSum(s[..half]) == DigitSum(s[half..])
}

method LuckyTicket(n: int, s: seq<char>) returns (result: bool)
  requires |s| == n
  requires n > 0
  requires n % 2 == 0
  ensures result == IsLuckyTicket(s)
{
  var a := 0;
  var b := 0;
  var half := |s| / 2;
  var i := 0;
  while i < |s|
  {
    if s[i] != '4' && s[i] != '7' {
      result := false;
      return;
    }
    var digit := (s[i] as int) - ('0' as int);
    if i < half {
      a := a + digit;
    } else {
      b := b + digit;
    }
    i := i + 1;
  }
  result := (a == b);
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
   /opt/homebrew/Cellar/dotnet@8/8.0.124/libexec/dotnet /Users/mchiesa/work/projects/2026-02-dafny-liftings/dafny-source/Binaries/Dafny.dll verify /Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0167_146_A/verified.dfy --verification-time-limit 60
   ```

5. If verification fails, read the error, fix the code, and retry.

6. Write the final result to `/Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0167_146_A/verified.dfy`.
   Also write `/Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0167_146_A/verify_result.json`:
   ```json
   {
     "verified": true/false,
     "attempts": N,
     "error": "last error if failed, null if verified"
   }
   ```

7. If you cannot verify after several attempts, save your best attempt as verified.dfy
   and set "verified": false in the result JSON.

IMPORTANT: Write output files to /Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0167_146_A/ (create the directory if needed).

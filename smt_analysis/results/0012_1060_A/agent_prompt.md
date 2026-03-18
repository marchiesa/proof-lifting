Make this Dafny program verify. Add loop invariants, assertions, ghost variables,
and/or lemmas as needed. Do NOT modify the ghost spec (functions, predicates) or the method
signature (requires, ensures). Only add proof annotations inside method bodies.

## Problem: Phone Numbers
Let's call a string a phone number if it has length 11 and fits the pattern "8xxxxxxxxxx", where each "x" is replaced by a digit.

For example, "80123456789" and "80000000000" are phone numbers, while "8012345678" and "79000000000" are not.

You have $$$n$$$ cards with digits, and you want to use them to make as many phone numbers as possible. Each card must be used in at most one phone number, and you don't have to use all cards. The phone numbers do not necessarily have to be distinct.

## File: /Users/mchiesa/work/projects/2026-02-dafny-liftings/dataset/0012_1060_A/task.dfy

```dafny
// Count occurrences of value v in sequence s
ghost function CountOccurrences(s: seq<int>, v: int): int
  decreases |s|
{
  if |s| == 0 then 0
  else (if s[|s|-1] == v then 1 else 0) + CountOccurrences(s[..|s|-1], v)
}

// Formalizes the problem statement: a valid assignment of cards to k phone numbers.
// assignment[i] == 0 means card i is unused.
// assignment[i] == j (1 <= j <= k) means card i belongs to phone number j.
// Each phone number uses exactly 11 cards, at least one of which has digit 8
// (capturing: phone numbers have length 11 and start with 8).
ghost predicate ValidPhoneAssignment(assignment: seq<int>, k: int, digits: seq<int>)
{
  |assignment| == |digits| &&
  k >= 0 &&
  (forall i | 0 <= i < |assignment| :: 0 <= assignment[i] <= k) &&
  (forall j | 1 <= j <= k ::
    CountOccurrences(assignment, j) == 11 &&
    (exists i | 0 <= i < |digits| :: assignment[i] == j && digits[i] == 8))
}

// Necessary and sufficient condition for forming k phone numbers from the cards:
//   - Each phone number requires 11 cards  =>  11 * k <= |digits|
//   - Each phone number requires at least one 8  =>  k <= count of 8s
ghost predicate Achievable(k: int, digits: seq<int>)
{
  k >= 0 && 11 * k <= |digits| && k <= CountOccurrences(digits, 8)
}

method PhoneNumbers(n: int, digits: seq<int>) returns (count: int)
  requires n == |digits|
  ensures Achievable(count, digits)
  ensures !Achievable(count + 1, digits)
{
  var cnt8 := 0;
  for i := 0 to |digits| {
    if digits[i] == 8 {
      cnt8 := cnt8 + 1;
    }
  }
  if cnt8 < n / 11 {
    count := cnt8;
  } else {
    count := n / 11;
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
   /opt/homebrew/Cellar/dotnet@8/8.0.124/libexec/dotnet /Users/mchiesa/work/projects/2026-02-dafny-liftings/dafny-source/Binaries/Dafny.dll verify /Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0012_1060_A/verified.dfy --verification-time-limit 60
   ```

5. If verification fails, read the error, fix the code, and retry.

6. Write the final result to `/Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0012_1060_A/verified.dfy`.
   Also write `/Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0012_1060_A/verify_result.json`:
   ```json
   {
     "verified": true/false,
     "attempts": N,
     "error": "last error if failed, null if verified"
   }
   ```

7. If you cannot verify after several attempts, save your best attempt as verified.dfy
   and set "verified": false in the result JSON.

IMPORTANT: Write output files to /Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0012_1060_A/ (create the directory if needed).

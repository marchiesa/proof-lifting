Make this Dafny program verify. Add loop invariants, assertions, ghost variables,
and/or lemmas as needed. Do NOT modify the ghost spec (functions, predicates) or the method
signature (requires, ensures). Only add proof annotations inside method bodies.

## Problem: Déjà Vu
A palindrome is a string that reads the same backward as forward. For example, the strings "z", "aaa", "aba", and "abccba" are palindromes, but "codeforces" and "ab" are not. You hate palindromes because they give you déjà vu.

There is a string $$$s$$$. You must insert exactly one character 'a' somewhere in $$$s$$$. If it is possible to create a string that is not a palindrome, you should find one example. Otherwise, you should report that it is impossible.

For example, suppose $$$s=$$$ "cbabc". By inserting an 'a', you can create "acbabc", "cababc", "cbaabc", "cbabac", or "cbabca". However "cbaabc" is a palindrome, so you must output one of the other options.

## File: /Users/mchiesa/work/projects/2026-02-dafny-liftings/dataset/0203_1504_A/task.dfy

```dafny
ghost predicate IsPalindrome(t: string)
{
  forall i | 0 <= i < |t| / 2 :: t[i] == t[|t| - 1 - i]
}

ghost function InsertCharAt(s: string, pos: nat): string
  requires pos <= |s|
{
  s[..pos] + "a" + s[pos..]
}

method DejaVu(s: string) returns (possible: bool, result: string)
  ensures possible ==>
    (exists pos | 0 <= pos <= |s| :: result == InsertCharAt(s, pos))
    && !IsPalindrome(result)
  ensures !possible ==>
    forall pos | 0 <= pos <= |s| :: IsPalindrome(InsertCharAt(s, pos))
{
  // Check if all characters are 'a'
  var allA := true;
  var i := 0;
  while i < |s| && allA {
    if s[i] != 'a' {
      allA := false;
    }
    i := i + 1;
  }

  if allA {
    possible := false;
    result := "";
    return;
  }

  // Check if s + "a" is a palindrome
  var sa := s + "a";
  var isPalin := true;
  var j := 0;
  while j < |sa| / 2 && isPalin {
    if sa[j] != sa[|sa| - 1 - j] {
      isPalin := false;
    }
    j := j + 1;
  }

  if isPalin {
    possible := true;
    result := "a" + s;
  } else {
    possible := true;
    result := s + "a";
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
   /opt/homebrew/Cellar/dotnet@8/8.0.124/libexec/dotnet /Users/mchiesa/work/projects/2026-02-dafny-liftings/dafny-source/Binaries/Dafny.dll verify /Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0203_1504_A/verified.dfy --verification-time-limit 60
   ```

5. If verification fails, read the error, fix the code, and retry.

6. Write the final result to `/Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0203_1504_A/verified.dfy`.
   Also write `/Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0203_1504_A/verify_result.json`:
   ```json
   {
     "verified": true/false,
     "attempts": N,
     "error": "last error if failed, null if verified"
   }
   ```

7. If you cannot verify after several attempts, save your best attempt as verified.dfy
   and set "verified": false in the result JSON.

IMPORTANT: Write output files to /Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0203_1504_A/ (create the directory if needed).

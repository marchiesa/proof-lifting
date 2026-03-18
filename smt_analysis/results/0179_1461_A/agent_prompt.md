Make this Dafny program verify. Add loop invariants, assertions, ghost variables,
and/or lemmas as needed. Do NOT modify the ghost spec (functions, predicates) or the method
signature (requires, ensures). Only add proof annotations inside method bodies.

## Problem: String Generation
One fall day Joe got bored because he couldn't find himself something interesting to do. Marty suggested Joe to generate a string of length $$$n$$$ to entertain him somehow. It didn't seem particularly difficult, but Joe's generated string had to follow these rules:

- the string may only contain characters 'a', 'b', or 'c';
- the maximum length of a substring of this string that is a palindrome does not exceed $$$k$$$.

A string $$$a$$$ is a substring of a string $$$b$$$ if $$$a$$$ can be obtained from $$$b$$$ by deletion of several (possibly, zero or all) characters from the beginning and several (possibly, zero or all) characters from the end. For example, strings "a", "bc", "abc" are substrings of a string "abc", while strings "ac", "ba", "cba" are not.

A string is a palindrome if it reads the same from the left to the right and from the right to the left. For example, strings "abccba", "abbba", "aba", "abacaba", "a", and "bacab" are palindromes, while strings "abcbba", "abb", and "ab" are not.

Now Joe wants to find any correct string. Help him! It can be proven that the answer always exists under the given constraints.

## File: /Users/mchiesa/work/projects/2026-02-dafny-liftings/dataset/0179_1461_A/task.dfy

```dafny
ghost predicate ValidChars(s: seq<char>)
{
  forall i | 0 <= i < |s| :: s[i] == 'a' || s[i] == 'b' || s[i] == 'c'
}

ghost predicate IsPalindrome(s: seq<char>)
{
  forall i | 0 <= i < |s| / 2 :: s[i] == s[|s| - 1 - i]
}

ghost predicate MaxPalindromeSubstringAtMostK(s: seq<char>, k: int)
{
  forall i, j | 0 <= i < j <= |s| && j - i > k :: !IsPalindrome(s[i..j])
}

method StringGeneration(n: int, k: int) returns (s: seq<char>)
  requires n >= 0
  requires k >= 1
  ensures |s| == n
  ensures ValidChars(s)
  ensures MaxPalindromeSubstringAtMostK(s, k)
{
  var pattern: seq<char> := ['a', 'b', 'c'];
  s := [];
  var i := 0;
  while i < n
  {
    s := s + [pattern[i % 3]];
    i := i + 1;
  }
}

method BuildExpected(n: int) returns (e: seq<char>)
  requires n >= 0
  ensures |e| == n
{
  var pattern: seq<char> := ['a', 'b', 'c'];
  e := [];
  var i := 0;
  while i < n
  {
    e := e + [pattern[i % 3]];
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
   /opt/homebrew/Cellar/dotnet@8/8.0.124/libexec/dotnet /Users/mchiesa/work/projects/2026-02-dafny-liftings/dafny-source/Binaries/Dafny.dll verify /Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0179_1461_A/verified.dfy --verification-time-limit 60
   ```

5. If verification fails, read the error, fix the code, and retry.

6. Write the final result to `/Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0179_1461_A/verified.dfy`.
   Also write `/Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0179_1461_A/verify_result.json`:
   ```json
   {
     "verified": true/false,
     "attempts": N,
     "error": "last error if failed, null if verified"
   }
   ```

7. If you cannot verify after several attempts, save your best attempt as verified.dfy
   and set "verified": false in the result JSON.

IMPORTANT: Write output files to /Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0179_1461_A/ (create the directory if needed).

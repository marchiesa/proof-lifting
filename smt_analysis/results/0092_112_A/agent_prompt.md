Make this Dafny program verify. Add loop invariants, assertions, ghost variables,
and/or lemmas as needed. Do NOT modify the ghost spec (functions, predicates) or the method
signature (requires, ensures). Only add proof annotations inside method bodies.

## Problem: Petya and Strings
Little Petya loves presents. His mum bought him two strings of the same size for his birthday. The strings consist of uppercase and lowercase Latin letters. Now Petya wants to compare those two strings lexicographically. The letters' case does not matter, that is an uppercase letter is considered equivalent to the corresponding lowercase letter. Help Petya perform the comparison.

## File: /Users/mchiesa/work/projects/2026-02-dafny-liftings/dataset/0092_112_A/task.dfy

```dafny
ghost function ToLower(c: char): char
{
  if 'A' <= c <= 'Z' then
    ((c as int - 'A' as int + 'a' as int) as char)
  else
    c
}

ghost predicate CIEqual(s: seq<char>, t: seq<char>)
{
  |s| == |t| &&
  forall i | 0 <= i < |s| :: ToLower(s[i]) == ToLower(t[i])
}

ghost predicate CILessThan(s: seq<char>, t: seq<char>)
{
  exists k | 0 <= k <= |s| && k <= |t| ::
    (forall j | 0 <= j < k :: ToLower(s[j]) == ToLower(t[j]))
    && ((k == |s| && k < |t|) || (k < |s| && k < |t| && ToLower(s[k]) < ToLower(t[k])))
}

method PetyaAndStrings(s: seq<char>, t: seq<char>) returns (result: int)
  ensures result == 0 <==> CIEqual(s, t)
  ensures result == -1 <==> CILessThan(s, t)
  ensures result == 1 <==> CILessThan(t, s)
{
  var len := if |s| < |t| then |s| else |t|;
  var i := 0;
  while i < len
  {
    var cs := s[i];
    var ct := t[i];
    if 'A' <= cs <= 'Z' {
      cs := (cs as int - 'A' as int + 'a' as int) as char;
    }
    if 'A' <= ct <= 'Z' {
      ct := (ct as int - 'A' as int + 'a' as int) as char;
    }
    if cs < ct {
      result := -1;
      return;
    } else if cs > ct {
      result := 1;
      return;
    }
    i := i + 1;
  }
  if |s| < |t| {
    result := -1;
  } else if |s| > |t| {
    result := 1;
  } else {
    result := 0;
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
   /opt/homebrew/Cellar/dotnet@8/8.0.124/libexec/dotnet /Users/mchiesa/work/projects/2026-02-dafny-liftings/dafny-source/Binaries/Dafny.dll verify /Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0092_112_A/verified.dfy --verification-time-limit 60
   ```

5. If verification fails, read the error, fix the code, and retry.

6. Write the final result to `/Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0092_112_A/verified.dfy`.
   Also write `/Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0092_112_A/verify_result.json`:
   ```json
   {
     "verified": true/false,
     "attempts": N,
     "error": "last error if failed, null if verified"
   }
   ```

7. If you cannot verify after several attempts, save your best attempt as verified.dfy
   and set "verified": false in the result JSON.

IMPORTANT: Write output files to /Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0092_112_A/ (create the directory if needed).

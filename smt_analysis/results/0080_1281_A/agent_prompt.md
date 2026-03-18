Make this Dafny program verify. Add loop invariants, assertions, ghost variables,
and/or lemmas as needed. Do NOT modify the ghost spec (functions, predicates) or the method
signature (requires, ensures). Only add proof annotations inside method bodies.

## Problem: Suffix Three
We just discovered a new data structure in our research group: a suffix three!

It's very useful for natural language processing. Given three languages and three suffixes, a suffix three can determine which language a sentence is written in.

It's super simple, 100% accurate, and doesn't involve advanced machine learning algorithms.

Let us tell you how it works.

- If a sentence ends with "po" the language is Filipino.
- If a sentence ends with "desu" or "masu" the language is Japanese.
- If a sentence ends with "mnida" the language is Korean.

Given this, we need you to implement a suffix three that can differentiate Filipino, Japanese, and Korean.

Oh, did I say three suffixes? I meant four.

## File: /Users/mchiesa/work/projects/2026-02-dafny-liftings/dataset/0080_1281_A/task.dfy

```dafny
ghost predicate EndsWith(s: string, suffix: string)
{
  |s| >= |suffix| && s[|s| - |suffix|..] == suffix
}

ghost predicate ValidSentence(s: string)
{
  EndsWith(s, "po") || EndsWith(s, "desu") || EndsWith(s, "masu") || EndsWith(s, "mnida")
}

ghost function ClassifySentence(s: string): string
  requires ValidSentence(s)
{
  if EndsWith(s, "po") then "FILIPINO"
  else if EndsWith(s, "desu") || EndsWith(s, "masu") then "JAPANESE"
  else "KOREAN"
}

ghost function ClassifyAll(sentences: seq<string>): seq<string>
  requires forall i :: 0 <= i < |sentences| ==> ValidSentence(sentences[i])
  decreases |sentences|
{
  if |sentences| == 0 then []
  else ClassifyAll(sentences[..|sentences|-1]) + [ClassifySentence(sentences[|sentences|-1])]
}

method SuffixThree(sentences: seq<string>) returns (results: seq<string>)
  requires forall i :: 0 <= i < |sentences| ==> ValidSentence(sentences[i])
  ensures results == ClassifyAll(sentences)
{
  results := [];
  for i := 0 to |sentences| {
    var s := sentences[i];
    var last := s[|s| - 1];
    if last == 'o' {
      results := results + ["FILIPINO"];
    } else if last == 'u' {
      results := results + ["JAPANESE"];
    } else {
      results := results + ["KOREAN"];
    }
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
   /opt/homebrew/Cellar/dotnet@8/8.0.124/libexec/dotnet /Users/mchiesa/work/projects/2026-02-dafny-liftings/dafny-source/Binaries/Dafny.dll verify /Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0080_1281_A/verified.dfy --verification-time-limit 60
   ```

5. If verification fails, read the error, fix the code, and retry.

6. Write the final result to `/Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0080_1281_A/verified.dfy`.
   Also write `/Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0080_1281_A/verify_result.json`:
   ```json
   {
     "verified": true/false,
     "attempts": N,
     "error": "last error if failed, null if verified"
   }
   ```

7. If you cannot verify after several attempts, save your best attempt as verified.dfy
   and set "verified": false in the result JSON.

IMPORTANT: Write output files to /Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0080_1281_A/ (create the directory if needed).

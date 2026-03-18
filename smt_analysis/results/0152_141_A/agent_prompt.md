Make this Dafny program verify. Add loop invariants, assertions, ghost variables,
and/or lemmas as needed. Do NOT modify the ghost spec (functions, predicates) or the method
signature (requires, ensures). Only add proof annotations inside method bodies.

## Problem: Amusing Joke
So, the New Year holidays are over. Santa Claus and his colleagues can take a rest and have guests at last. When two "New Year and Christmas Men" meet, thear assistants cut out of cardboard the letters from the guest's name and the host's name in honor of this event. Then the hung the letters above the main entrance. One night, when everyone went to bed, someone took all the letters of our characters' names. Then he may have shuffled the letters and put them in one pile in front of the door.

The next morning it was impossible to find the culprit who had made the disorder. But everybody wondered whether it is possible to restore the names of the host and his guests from the letters lying at the door? That is, we need to verify that there are no extra letters, and that nobody will need to cut more letters.

Help the "New Year and Christmas Men" and their friends to cope with this problem. You are given both inscriptions that hung over the front door the previous night, and a pile of letters that were found at the front door next morning.

## File: /Users/mchiesa/work/projects/2026-02-dafny-liftings/dataset/0152_141_A/task.dfy

```dafny
ghost function CountChar(s: seq<char>, c: char): nat
  decreases |s|
{
  if |s| == 0 then 0
  else (if s[|s|-1] == c then 1 else 0) + CountChar(s[..|s|-1], c)
}

// The pile has the same letters as the two names: no extras, no missing
ghost predicate SameLetters(a: seq<char>, b: seq<char>)
{
  |a| == |b| &&
  (forall i | 0 <= i < |a| :: CountChar(a, a[i]) == CountChar(b, a[i])) &&
  (forall i | 0 <= i < |b| :: CountChar(a, b[i]) == CountChar(b, b[i]))
}

ghost predicate IsSorted(s: seq<char>)
{
  forall i | 0 <= i < |s| - 1 :: s[i] <= s[i + 1]
}

method SortCharSeq(s: seq<char>) returns (sorted: array<char>)
  ensures sorted.Length == |s|
  ensures IsSorted(sorted[..])
  ensures SameLetters(sorted[..], s)
{
  sorted := new char[|s|];
  var i := 0;
  while i < |s| {
    sorted[i] := s[i];
    i := i + 1;
  }
  i := 0;
  while i < sorted.Length {
    var minIdx := i;
    var j := i + 1;
    while j < sorted.Length {
      if sorted[j] < sorted[minIdx] {
        minIdx := j;
      }
      j := j + 1;
    }
    if minIdx != i {
      var tmp := sorted[i];
      sorted[i] := sorted[minIdx];
      sorted[minIdx] := tmp;
    }
    i := i + 1;
  }
}

method AmusingJoke(guest: seq<char>, host: seq<char>, pile: seq<char>) returns (result: bool)
  ensures result == SameLetters(guest + host, pile)
{
  var ab := guest + host;
  var sortedAB := SortCharSeq(ab);
  var sortedC := SortCharSeq(pile);
  if sortedAB.Length != sortedC.Length {
    return false;
  }
  var i := 0;
  while i < sortedAB.Length {
    if sortedAB[i] != sortedC[i] {
      return false;
    }
    i := i + 1;
  }
  return true;
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
   /opt/homebrew/Cellar/dotnet@8/8.0.124/libexec/dotnet /Users/mchiesa/work/projects/2026-02-dafny-liftings/dafny-source/Binaries/Dafny.dll verify /Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0152_141_A/verified.dfy --verification-time-limit 60
   ```

5. If verification fails, read the error, fix the code, and retry.

6. Write the final result to `/Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0152_141_A/verified.dfy`.
   Also write `/Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0152_141_A/verify_result.json`:
   ```json
   {
     "verified": true/false,
     "attempts": N,
     "error": "last error if failed, null if verified"
   }
   ```

7. If you cannot verify after several attempts, save your best attempt as verified.dfy
   and set "verified": false in the result JSON.

IMPORTANT: Write output files to /Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0152_141_A/ (create the directory if needed).

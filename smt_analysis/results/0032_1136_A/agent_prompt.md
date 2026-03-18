Make this Dafny program verify. Add loop invariants, assertions, ghost variables,
and/or lemmas as needed. Do NOT modify the ghost spec (functions, predicates) or the method
signature (requires, ensures). Only add proof annotations inside method bodies.

## Problem: Nastya Is Reading a Book
After lessons Nastya decided to read a book. The book contains $$$n$$$ chapters, going one after another, so that one page of the book belongs to exactly one chapter and each chapter contains at least one page.

Yesterday evening Nastya did not manage to finish reading the book, so she marked the page with number $$$k$$$ as the first page which was not read (i.e. she read all pages from the $$$1$$$-st to the $$$(k-1)$$$-th).

The next day Nastya's friend Igor came and asked her, how many chapters remain to be read by Nastya? Nastya is too busy now, so she asks you to compute the number of chapters she has not completely read yet (i.e. the number of chapters she has not started to read or has finished reading somewhere in the middle).

## File: /Users/mchiesa/work/projects/2026-02-dafny-liftings/dataset/0032_1136_A/task.dfy

```dafny
// A chapter is not completely read if it contains at least one unread page.
// Page p is unread when p >= k (k is the first unread page).
ghost predicate ChapterNotCompletelyRead(chapter: (int, int), k: int)
{
  exists p | chapter.0 <= p <= chapter.1 :: p >= k
}

// Count chapters that are not completely read.
ghost function CountNotCompletelyRead(chapters: seq<(int, int)>, k: int): int
  decreases |chapters|
{
  if |chapters| == 0 then 0
  else
    CountNotCompletelyRead(chapters[..|chapters|-1], k)
    + (if ChapterNotCompletelyRead(chapters[|chapters|-1], k) then 1 else 0)
}

method NastyaBook(chapters: seq<(int, int)>, k: int) returns (count: int)
  requires forall i | 0 <= i < |chapters| :: chapters[i].0 <= chapters[i].1
  requires forall i | 0 <= i < |chapters| - 1 :: chapters[i].1 < chapters[i+1].0
  requires k >= 1
  ensures count == CountNotCompletelyRead(chapters, k)
{
  var i := 0;
  while i < |chapters|
  {
    var (_, y) := chapters[i];
    if y >= k {
      count := |chapters| - i;
      return;
    }
    i := i + 1;
  }
  count := 0;
  return;
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
   /opt/homebrew/Cellar/dotnet@8/8.0.124/libexec/dotnet /Users/mchiesa/work/projects/2026-02-dafny-liftings/dafny-source/Binaries/Dafny.dll verify /Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0032_1136_A/verified.dfy --verification-time-limit 60
   ```

5. If verification fails, read the error, fix the code, and retry.

6. Write the final result to `/Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0032_1136_A/verified.dfy`.
   Also write `/Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0032_1136_A/verify_result.json`:
   ```json
   {
     "verified": true/false,
     "attempts": N,
     "error": "last error if failed, null if verified"
   }
   ```

7. If you cannot verify after several attempts, save your best attempt as verified.dfy
   and set "verified": false in the result JSON.

IMPORTANT: Write output files to /Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0032_1136_A/ (create the directory if needed).

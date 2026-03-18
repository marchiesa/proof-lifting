Make this Dafny program verify. Add loop invariants, assertions, ghost variables,
and/or lemmas as needed. Do NOT modify the ghost spec (functions, predicates) or the method
signature (requires, ensures). Only add proof annotations inside method bodies.

## Problem: Unique Bid Auction
There is a game called "Unique Bid Auction". You can read more about it here: https://en.wikipedia.org/wiki/Unique_bid_auction (though you don't have to do it to solve this problem).

Let's simplify this game a bit. Formally, there are $$$n$$$ participants, the $$$i$$$-th participant chose the number $$$a_i$$$. The winner of the game is such a participant that the number he chose is unique (i. e. nobody else chose this number except him) and is minimal (i. e. among all unique values of $$$a$$$ the minimum one is the winning one).

Your task is to find the index of the participant who won the game (or -1 if there is no winner). Indexing is $$$1$$$-based, i. e. the participants are numbered from $$$1$$$ to $$$n$$$.

You have to answer $$$t$$$ independent test cases.

## File: /Users/mchiesa/work/projects/2026-02-dafny-liftings/dataset/0182_1454_B/task.dfy

```dafny
ghost function Count(a: seq<int>, v: int): int
  decreases |a|
{
  if |a| == 0 then 0
  else (if a[|a|-1] == v then 1 else 0) + Count(a[..|a|-1], v)
}

ghost predicate IsUniqueBid(a: seq<int>, i: int)
  requires 0 <= i < |a|
{
  Count(a, a[i]) == 1
}

ghost predicate NoUniqueBids(a: seq<int>)
{
  forall i | 0 <= i < |a| :: Count(a, a[i]) != 1
}

ghost predicate IsMinimumUniqueBid(a: seq<int>, i: int)
  requires 0 <= i < |a|
{
  IsUniqueBid(a, i) &&
  forall j | 0 <= j < |a| :: (Count(a, a[j]) == 1 ==> a[i] <= a[j])
}

method UniqueBidAuction(a: seq<int>) returns (winner: int)
  ensures NoUniqueBids(a) <==> (winner == -1)
  ensures winner != -1 ==> (1 <= winner <= |a| && IsMinimumUniqueBid(a, winner - 1))
{
  winner := -1;
  var minVal := 0;
  var found := false;

  var i := 0;
  while i < |a|
  {
    var count := 0;
    var j := 0;
    while j < |a|
    {
      if a[j] == a[i] {
        count := count + 1;
      }
      j := j + 1;
    }
    if count == 1 && (!found || a[i] < minVal) {
      minVal := a[i];
      winner := i + 1;
      found := true;
    }
    i := i + 1;
  }
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
   /opt/homebrew/Cellar/dotnet@8/8.0.124/libexec/dotnet /Users/mchiesa/work/projects/2026-02-dafny-liftings/dafny-source/Binaries/Dafny.dll verify /Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0182_1454_B/verified.dfy --verification-time-limit 60
   ```

5. If verification fails, read the error, fix the code, and retry.

6. Write the final result to `/Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0182_1454_B/verified.dfy`.
   Also write `/Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0182_1454_B/verify_result.json`:
   ```json
   {
     "verified": true/false,
     "attempts": N,
     "error": "last error if failed, null if verified"
   }
   ```

7. If you cannot verify after several attempts, save your best attempt as verified.dfy
   and set "verified": false in the result JSON.

IMPORTANT: Write output files to /Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0182_1454_B/ (create the directory if needed).

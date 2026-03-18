Make this Dafny program verify. Add loop invariants, assertions, ghost variables,
and/or lemmas as needed. Do NOT modify the ghost spec (functions, predicates) or the method
signature (requires, ensures). Only add proof annotations inside method bodies.

## Problem: Snowball
Today's morning was exceptionally snowy. Meshanya decided to go outside and noticed a huge snowball rolling down the mountain! Luckily, there are two stones on that mountain.

Initially, snowball is at height $$$h$$$ and it has weight $$$w$$$. Each second the following sequence of events happens: snowball's weights increases by $$$i$$$, where $$$i$$$ — is the current height of snowball, then snowball hits the stone (if it's present at the current height), then snowball moves one meter down. If the snowball reaches height zero, it stops.

There are exactly two stones on the mountain. First stone has weight $$$u_1$$$ and is located at height $$$d_1$$$, the second one — $$$u_2$$$ and $$$d_2$$$ respectively. When the snowball hits either of two stones, it loses weight equal to the weight of that stone. If after this snowball has negative weight, then its weight becomes zero, but the snowball continues moving as before.

Find the weight of the snowball when it stops moving, that is, it reaches height 0.

## File: /Users/mchiesa/work/projects/2026-02-dafny-liftings/dataset/0033_1099_A/task.dfy

```dafny
// Clamp negative weights to zero, per the problem rules
ghost function Max0(x: int): int {
  if x < 0 then 0 else x
}

// "Each second the following sequence of events happens" at a given height:
//  1. Snowball's weight increases by current height
//  2. If stone 1 is at this height, snowball loses u1 weight (clamped to 0)
//  3. If stone 2 is at this height, snowball loses u2 weight (clamped to 0)
ghost function WeightAfterHeight(weight: int, height: int,
                           u1: int, d1: int, u2: int, d2: int): int
{
  var afterGain  := weight + height;
  var afterStone1 := if height == d1 then Max0(afterGain - u1) else afterGain;
  var afterStone2 := if height == d2 then Max0(afterStone1 - u2) else afterStone1;
  afterStone2
}

// The descending sequence of heights the snowball visits: [h, h-1, ..., 1, 0]
ghost function Heights(h: int): seq<int>
  decreases if h >= 0 then h + 1 else 0
{
  if h < 0 then []
  else [h] + Heights(h - 1)
}

// The snowball's weight after rolling through the given sequence of heights
ghost function RollThrough(w: int, heights: seq<int>,
                     u1: int, d1: int, u2: int, d2: int): int
  decreases |heights|
{
  if |heights| == 0 then w
  else RollThrough(WeightAfterHeight(w, heights[0], u1, d1, u2, d2),
                   heights[1..], u1, d1, u2, d2)
}

method Snowball(w: int, h: int, u1: int, d1: int, u2: int, d2: int) returns (finalWeight: int)
  ensures finalWeight == RollThrough(w, Heights(h), u1, d1, u2, d2)
{
  finalWeight := w;
  var i := h;
  while i >= 0 {
    finalWeight := finalWeight + i;
    if i == d1 {
      finalWeight := finalWeight - u1;
      if finalWeight < 0 {
        finalWeight := 0;
      }
    }
    if i == d2 {
      finalWeight := finalWeight - u2;
      if finalWeight < 0 {
        finalWeight := 0;
      }
    }
    i := i - 1;
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
   /opt/homebrew/Cellar/dotnet@8/8.0.124/libexec/dotnet /Users/mchiesa/work/projects/2026-02-dafny-liftings/dafny-source/Binaries/Dafny.dll verify /Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0033_1099_A/verified.dfy --verification-time-limit 60
   ```

5. If verification fails, read the error, fix the code, and retry.

6. Write the final result to `/Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0033_1099_A/verified.dfy`.
   Also write `/Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0033_1099_A/verify_result.json`:
   ```json
   {
     "verified": true/false,
     "attempts": N,
     "error": "last error if failed, null if verified"
   }
   ```

7. If you cannot verify after several attempts, save your best attempt as verified.dfy
   and set "verified": false in the result JSON.

IMPORTANT: Write output files to /Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0033_1099_A/ (create the directory if needed).

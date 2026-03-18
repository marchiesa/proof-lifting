Make this Dafny program verify. Add loop invariants, assertions, ghost variables,
and/or lemmas as needed. Do NOT modify the ghost spec (functions, predicates) or the method
signature (requires, ensures). Only add proof annotations inside method bodies.

## Problem: Blackjack
One rainy gloomy evening when all modules hid in the nearby cafes to drink hot energetic cocktails, the Hexadecimal virus decided to fly over the Mainframe to look for a Great Idea. And she has found one!

Why not make her own Codeforces, with blackjack and other really cool stuff? Many people will surely be willing to visit this splendid shrine of high culture.

In Mainframe a standard pack of 52 cards is used to play blackjack. The pack contains cards of 13 values: 2, 3, 4, 5, 6, 7, 8, 9, 10, jacks, queens, kings and aces. Each value also exists in one of four suits: hearts, diamonds, clubs and spades. Also, each card earns some value in points assigned to it: cards with value from two to ten earn from 2 to 10 points, correspondingly. An ace can either earn 1 or 11, whatever the player wishes. The picture cards (king, queen and jack) earn 10 points. The number of points a card earns does not depend on the suit. The rules of the game are very simple. The player gets two cards, if the sum of points of those cards equals n, then the player wins, otherwise the player loses.

The player has already got the first card, it's the queen of spades. To evaluate chances for victory, you should determine how many ways there are to get the second card so that the sum of points exactly equals n.

## File: /Users/mchiesa/work/projects/2026-02-dafny-liftings/dataset/0005_104_A/task.dfy

```dafny
// --- Specification: formalizes the Blackjack problem statement ---

// Point values for each of the 13 face values in a standard deck.
// Face 0=Two, 1=Three, ..., 8=Ten, 9=Jack, 10=Queen, 11=King, 12=Ace.
ghost function FacePoints(face: int): seq<int>
  requires 0 <= face <= 12
{
  if face <= 8 then [face + 2]       // Two(2) through Ten(10)
  else if face <= 11 then [10]        // Jack, Queen, King: 10 points
  else [1, 11]                        // Ace: 1 or 11 points
}

// A card with the given face value can score exactly p points.
ghost predicate CanScore(face: int, p: int)
  requires 0 <= face <= 12
{
  exists k | 0 <= k < |FacePoints(face)| :: FacePoints(face)[k] == p
}

// Suits remaining per face value in the deck after dealing the queen of spades.
// Queens (face 10) have 3 remaining suits; all other faces have 4.
ghost function SuitsAvailable(face: int): int
  requires 0 <= face <= 12
{
  if face == 10 then 3 else 4
}

// The 13 face values in a standard deck.
ghost function AllFaces(): seq<int>
{
  [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]
}

// Count of available cards across the given face values whose point value
// can combine with 10 (the queen of spades) to total exactly n.
ghost function CountWinningCards(n: int, faces: seq<int>): int
  decreases |faces|
{
  if |faces| == 0 then 0
  else
    var face := faces[|faces| - 1];
    var rest := CountWinningCards(n, faces[..|faces| - 1]);
    if 0 <= face <= 12 && CanScore(face, n - 10)
    then rest + SuitsAvailable(face)
    else rest
}

// Total number of second-card draws that win: sum over all 13 face values
// of (suits available) for each face that can score (n - 10) points.
ghost function ExpectedWays(n: int): int
{
  CountWinningCards(n, AllFaces())
}

// --- Implementation (unmodified) ---

method Blackjack(n: int) returns (ways: int)
  ensures ways == ExpectedWays(n)
{
  var vals: seq<seq<int>> := [[10], [2], [3], [4], [5], [6], [7], [8], [9], [10], [10], [10], [1, 11]];

  ways := 0;
  var i := 0;
  while i < |vals|
  {
    var x := vals[i];
    var j := 0;
    while j < |x|
    {
      var y := x[j];
      if y + 10 == n {
        ways := ways + 3;
        if i != 0 {
          ways := ways + 1;
        }
      }
      j := j + 1;
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
   /opt/homebrew/Cellar/dotnet@8/8.0.124/libexec/dotnet /Users/mchiesa/work/projects/2026-02-dafny-liftings/dafny-source/Binaries/Dafny.dll verify /Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0005_104_A/verified.dfy --verification-time-limit 60
   ```

5. If verification fails, read the error, fix the code, and retry.

6. Write the final result to `/Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0005_104_A/verified.dfy`.
   Also write `/Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0005_104_A/verify_result.json`:
   ```json
   {
     "verified": true/false,
     "attempts": N,
     "error": "last error if failed, null if verified"
   }
   ```

7. If you cannot verify after several attempts, save your best attempt as verified.dfy
   and set "verified": false in the result JSON.

IMPORTANT: Write output files to /Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0005_104_A/ (create the directory if needed).

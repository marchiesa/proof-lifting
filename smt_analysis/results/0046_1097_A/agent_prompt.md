Make this Dafny program verify. Add loop invariants, assertions, ghost variables,
and/or lemmas as needed. Do NOT modify the ghost spec (functions, predicates) or the method
signature (requires, ensures). Only add proof annotations inside method bodies.

## Problem: Gennady and a Card Game
Gennady owns a small hotel in the countryside where he lives a peaceful life. He loves to take long walks, watch sunsets and play cards with tourists staying in his hotel. His favorite game is called "Mau-Mau".

To play Mau-Mau, you need a pack of $$$52$$$ cards. Each card has a suit (Diamonds — D, Clubs — C, Spades — S, or Hearts — H), and a rank (2, 3, 4, 5, 6, 7, 8, 9, T, J, Q, K, or A).

At the start of the game, there is one card on the table and you have five cards in your hand. You can play a card from your hand if and only if it has the same rank or the same suit as the card on the table.

In order to check if you'd be a good playing partner, Gennady has prepared a task for you. Given the card on the table and five cards in your hand, check if you can play at least one card.

## File: /Users/mchiesa/work/projects/2026-02-dafny-liftings/dataset/0046_1097_A/task.dfy

```dafny
// --- Formal specification for Mau-Mau card game ---

// The 13 valid ranks in the deck
ghost predicate IsRank(c: char)
{
  c in {'2', '3', '4', '5', '6', '7', '8', '9', 'T', 'J', 'Q', 'K', 'A'}
}

// The 4 valid suits in the deck
ghost predicate IsSuit(c: char)
{
  c in {'D', 'C', 'S', 'H'}
}

// A valid card: exactly 2 characters, rank then suit
ghost predicate IsCard(s: string)
{
  |s| == 2 && IsRank(s[0]) && IsSuit(s[1])
}

// A valid Mau-Mau hand: exactly 5 valid cards
ghost predicate IsHand(hand: seq<string>)
{
  |hand| == 5 && forall i | 0 <= i < |hand| :: IsCard(hand[i])
}

// The rank of a card (first character)
ghost function RankOf(card: string): char
  requires |card| >= 1
{
  card[0]
}

// The suit of a card (second character)
ghost function SuitOf(card: string): char
  requires |card| >= 2
{
  card[1]
}

// A hand card is playable on a table card iff it shares rank or suit
ghost predicate IsPlayable(handCard: string, tableCard: string)
  requires |handCard| >= 2 && |tableCard| >= 2
{
  RankOf(handCard) == RankOf(tableCard) || SuitOf(handCard) == SuitOf(tableCard)
}

// The player can make a move iff at least one card in hand is playable on the table card
ghost predicate HasPlayableCard(hand: seq<string>, tableCard: string)
  requires |tableCard| >= 2
  requires forall i | 0 <= i < |hand| :: |hand[i]| >= 2
{
  exists i | 0 <= i < |hand| :: IsPlayable(hand[i], tableCard)
}

method CardGame(table: string, hand: seq<string>) returns (canPlay: bool)
  requires IsCard(table)
  requires IsHand(hand)
  ensures canPlay == HasPlayableCard(hand, table)
{
  canPlay := false;
  var i := 0;
  while i < |hand|
  {
    if |hand[i]| >= 2 && |table| >= 2 {
      if hand[i][0] == table[0] || hand[i][1] == table[1] {
        canPlay := true;
        return;
      }
    }
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
   /opt/homebrew/Cellar/dotnet@8/8.0.124/libexec/dotnet /Users/mchiesa/work/projects/2026-02-dafny-liftings/dafny-source/Binaries/Dafny.dll verify /Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0046_1097_A/verified.dfy --verification-time-limit 60
   ```

5. If verification fails, read the error, fix the code, and retry.

6. Write the final result to `/Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0046_1097_A/verified.dfy`.
   Also write `/Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0046_1097_A/verify_result.json`:
   ```json
   {
     "verified": true/false,
     "attempts": N,
     "error": "last error if failed, null if verified"
   }
   ```

7. If you cannot verify after several attempts, save your best attempt as verified.dfy
   and set "verified": false in the result JSON.

IMPORTANT: Write output files to /Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0046_1097_A/ (create the directory if needed).

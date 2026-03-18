Make this Dafny program verify. Add loop invariants, assertions, ghost variables,
and/or lemmas as needed. Do NOT modify the ghost spec (functions, predicates) or the method
signature (requires, ensures). Only add proof annotations inside method bodies.

## Problem: Card Game
Two players decided to play one interesting card game.

There is a deck of $$$n$$$ cards, with values from $$$1$$$ to $$$n$$$. The values of cards are pairwise different (this means that no two different cards have equal values). At the beginning of the game, the deck is completely distributed between players such that each player has at least one card.

The game goes as follows: on each turn, each player chooses one of their cards (whichever they want) and puts on the table, so that the other player doesn't see which card they chose. After that, both cards are revealed, and the player, value of whose card was larger, takes both cards in his hand. Note that as all cards have different values, one of the cards will be strictly larger than the other one. Every card may be played any amount of times. The player loses if he doesn't have any cards.

For example, suppose that $$$n = 5$$$, the first player has cards with values $$$2$$$ and $$$3$$$, and the second player has cards with values $$$1$$$, $$$4$$$, $$$5$$$. Then one possible flow of the game is:

- The first player chooses the card $$$3$$$. The second player chooses the card $$$1$$$. As $$$3>1$$$, the first player gets both cards. Now the first player has cards $$$1$$$, $$$2$$$, $$$3$$$, the second player has cards $$$4$$$, $$$5$$$.
- The first player chooses the card $$$3$$$. The second player chooses the card $$$4$$$. As $$$3<4$$$, the second player gets both cards. Now the first player has cards $$$1$$$, $$$2$$$. The second player has cards $$$3$$$, $$$4$$$, $$$5$$$.
- The first player chooses the card $$$1$$$. The second player chooses the card $$$3$$$. As $$$1<3$$$, the second player gets both cards. Now the first player has only the card $$$2$$$. The second player has cards $$$1$$$, $$$3$$$, $$$4$$$, $$$5$$$.
- The first player chooses the card $$$2$$$. The second player chooses the card $$$4$$$. As $$$2<4$$$, the second player gets both cards. Now the first player is out of cards and loses. Therefore, the second player wins.

Who will win if both players are playing optimally? It can be shown that one of the players has a winning strategy.

## File: /Users/mchiesa/work/projects/2026-02-dafny-liftings/dataset/0086_1270_A/task.dfy

```dafny
// ── Spec helpers ──────────────────────────────────────────────────────

ghost function SeqToSet(s: seq<int>): set<int>
  decreases |s|
{
  if |s| == 0 then {} else {s[|s|-1]} + SeqToSet(s[..|s|-1])
}

ghost predicate NoDuplicates(s: seq<int>)
{
  forall i, j | 0 <= i < j < |s| :: s[i] != s[j]
}

// Cards 1..n are split into two non-empty, disjoint hands that cover the full deck.
ghost predicate ValidDeck(n: int, a: seq<int>, b: seq<int>)
{
  n >= 2
  && |a| >= 1
  && |b| >= 1
  && NoDuplicates(a)
  && NoDuplicates(b)
  && SeqToSet(a) !! SeqToSet(b)
  && SeqToSet(a) + SeqToSet(b) == set i | 1 <= i <= n :: i
}

// Minimax game-tree search:
//   Player 1 wins immediately when Player 2's hand is empty.
//   Player 1 loses when their own hand is empty or the step budget runs out.
//   Otherwise Player 1 wins iff they can pick SOME card c1 such that
//   for EVERY card c2 Player 2 might play, the round's winner takes both
//   cards and Player 1 still wins the resulting subgame.
ghost predicate Player1CanWin(S1: set<int>, S2: set<int>, steps: nat)
  decreases steps
{
  if S2 == {} then true
  else if S1 == {} || steps == 0 then false
  else exists c1 | c1 in S1 :: forall c2 | c2 in S2 ::
    if c1 > c2 then Player1CanWin(S1 + {c2}, S2 - {c2}, steps - 1)
    else Player1CanWin(S1 - {c1}, S2 + {c1}, steps - 1)
}

// Player 1 wins the card game: there exists some number of steps
// at which a winning strategy exists.
ghost predicate Player1WinsGame(S1: set<int>, S2: set<int>, bound: nat)
{
  exists steps: nat :: Player1CanWin(S1, S2, steps)
}

// ── Method with specification ─────────────────────────────────────────

method CardGame(n: int, k1: int, k2: int, a: seq<int>, b: seq<int>) returns (firstPlayerWins: bool)
  requires ValidDeck(n, a, b)
  requires k1 == |a| && k2 == |b|
  ensures firstPlayerWins <==> Player1WinsGame(SeqToSet(a), SeqToSet(b), n)
{
  var maxA := a[0];
  var i := 1;
  while i < |a|
  {
    if a[i] > maxA {
      maxA := a[i];
    }
    i := i + 1;
  }

  var maxB := b[0];
  var j := 1;
  while j < |b|
  {
    if b[j] > maxB {
      maxB := b[j];
    }
    j := j + 1;
  }

  firstPlayerWins := maxA > maxB;
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
   /opt/homebrew/Cellar/dotnet@8/8.0.124/libexec/dotnet /Users/mchiesa/work/projects/2026-02-dafny-liftings/dafny-source/Binaries/Dafny.dll verify /Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0086_1270_A/verified.dfy --verification-time-limit 60
   ```

5. If verification fails, read the error, fix the code, and retry.

6. Write the final result to `/Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0086_1270_A/verified.dfy`.
   Also write `/Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0086_1270_A/verify_result.json`:
   ```json
   {
     "verified": true/false,
     "attempts": N,
     "error": "last error if failed, null if verified"
   }
   ```

7. If you cannot verify after several attempts, save your best attempt as verified.dfy
   and set "verified": false in the result JSON.

IMPORTANT: Write output files to /Users/mchiesa/work/projects/2026-02-dafny-liftings/smt_analysis/results/0086_1270_A/ (create the directory if needed).

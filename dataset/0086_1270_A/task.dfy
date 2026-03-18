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
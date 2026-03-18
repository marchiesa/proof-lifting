// Can position a be transformed to position b in exactly n moves,
// where each move chooses k ∈ [1, 10] and performs a := a + k or a := a - k?
ghost predicate Reachable(a: int, b: int, n: int)
  decreases if n < 0 then 0 else n
{
  if n <= 0 then
    n == 0 && a == b
  else
    exists k | 1 <= k <= 10 ::
      Reachable(a + k, b, n - 1) || Reachable(a - k, b, n - 1)
}

// moves is the minimum number of such moves needed to transform a into b
ghost predicate IsMinMoves(a: int, b: int, moves: int) {
  moves >= 0
  && Reachable(a, b, moves)
  && forall n :: 0 <= n < moves ==> !Reachable(a, b, n)
}

method MinMoves(a: int, b: int) returns (moves: int)
  ensures IsMinMoves(a, b, moves)
{
  var lo := a;
  var hi := b;
  if lo > hi {
    lo := b;
    hi := a;
  }
  var diff := hi - lo;
  moves := diff / 10;
  if diff % 10 != 0 {
    moves := moves + 1;
  }
}
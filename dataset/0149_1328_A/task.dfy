ghost predicate IsDivisibleAfterMoves(a: int, b: int, moves: int)
  requires b > 0
{
  moves >= 0 && (a + moves) % b == 0
}

ghost predicate IsMinimumMoves(a: int, b: int, moves: int)
  requires b > 0
{
  IsDivisibleAfterMoves(a, b, moves) &&
  forall m | 0 <= m < moves :: !IsDivisibleAfterMoves(a, b, m)
}

method DivisibilityProblem(a: int, b: int) returns (moves: int)
  requires a >= 1 && b >= 1
  ensures IsMinimumMoves(a, b, moves)
{
  moves := (b - a % b) % b;
}
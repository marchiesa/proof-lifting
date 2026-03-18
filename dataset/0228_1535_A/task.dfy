// Winner of a match: the player with higher skill wins
ghost function MatchWinner(a: int, b: int): int {
  if a > b then a else b
}

// Count how many of the four skill values are strictly greater than v
ghost function CountGreater(v: int, s1: int, s2: int, s3: int, s4: int): int {
  (if s1 > v then 1 else 0) + (if s2 > v then 1 else 0) +
  (if s3 > v then 1 else 0) + (if s4 > v then 1 else 0)
}

// A player with skill v is among the top two if at most one player has higher skill
ghost predicate IsTopTwo(v: int, s1: int, s2: int, s3: int, s4: int) {
  CountGreater(v, s1, s2, s3, s4) <= 1
}

// The tournament is fair if both semifinal winners are among the top-two skilled players
ghost predicate FairTournament(s1: int, s2: int, s3: int, s4: int) {
  IsTopTwo(MatchWinner(s1, s2), s1, s2, s3, s4) &&
  IsTopTwo(MatchWinner(s3, s4), s1, s2, s3, s4)
}

method FairPlayoff(s1: int, s2: int, s3: int, s4: int) returns (fair: bool)
  requires s1 != s2 && s1 != s3 && s1 != s4 && s2 != s3 && s2 != s4 && s3 != s4
  ensures fair == FairTournament(s1, s2, s3, s4)
{
  var min12 := if s1 < s2 then s1 else s2;
  var max12 := if s1 > s2 then s1 else s2;
  var min34 := if s3 < s4 then s3 else s4;
  var max34 := if s3 > s4 then s3 else s4;

  if min34 > max12 || min12 > max34 {
    fair := false;
  } else {
    fair := true;
  }
}
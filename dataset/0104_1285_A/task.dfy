ghost function CountChar(s: string, c: char): int
  decreases |s|
{
  if |s| == 0 then 0
  else CountChar(s[..|s|-1], c) + (if s[|s|-1] == c then 1 else 0)
}

// A position p is reachable if we can choose how many L-commands to execute
// (0..total_L) and how many R-commands to execute (0..total_R) such that
// the net displacement nr - nl equals p. This models the problem: each
// command is independently either executed (keeping its effect) or ignored.
ghost predicate Reachable(s: string, p: int)
{
  var l := CountChar(s, 'L');
  var r := CountChar(s, 'R');
  exists nl: int, nr: int | 0 <= nl <= l && 0 <= nr <= r :: p == nr - nl
}

ghost function ReachablePositions(s: string): set<int>
{
  var l := CountChar(s, 'L');
  var r := CountChar(s, 'R');
  set p: int | -l <= p <= r && Reachable(s, p)
}

method MezoPlayingZoma(s: string) returns (positions: int)
  requires forall i | 0 <= i < |s| :: s[i] == 'L' || s[i] == 'R'
  ensures positions == |ReachablePositions(s)|
{
  var l := 0;
  var r := 0;
  for i := 0 to |s| {
    if s[i] == 'L' {
      l := l + 1;
    } else if s[i] == 'R' {
      r := r + 1;
    }
  }
  positions := l + r + 1;
}
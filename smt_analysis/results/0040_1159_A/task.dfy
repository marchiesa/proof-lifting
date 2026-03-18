ghost function Delta(c: char): int
{
  if c == '-' then -1 else 1
}

ghost function SumDeltas(s: seq<char>): int
  decreases |s|
{
  if |s| == 0 then 0
  else SumDeltas(s[..|s|-1]) + Delta(s[|s|-1])
}

// A valid execution: starting with `init` stones (>= 0), the pile
// never goes negative at any point during the sequence of operations.
ghost predicate ValidExecution(s: seq<char>, init: int)
{
  init >= 0 &&
  forall k | 0 <= k <= |s| :: init + SumDeltas(s[..k]) >= 0
}

ghost function FinalPileSize(s: seq<char>, init: int): int
{
  init + SumDeltas(s)
}

method PileOfStones(s: seq<char>) returns (result: int)
  // There exists a valid initial pile size that yields this result
  ensures exists init: nat :: ValidExecution(s, init) && FinalPileSize(s, init) == result
  // No valid initial pile size yields a smaller final pile
  ensures forall init: nat :: ValidExecution(s, init) ==> FinalPileSize(s, init) >= result
{
  result := 0;
  var i := 0;
  while i < |s|
  {
    if s[i] == '-' {
      if result > 0 {
        result := result - 1;
      }
    } else {
      result := result + 1;
    }
    i := i + 1;
  }
}
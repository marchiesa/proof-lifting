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
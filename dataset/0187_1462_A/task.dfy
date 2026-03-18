// --- Specification: Polycarp's Whiteboard Writing Process ---

// Elements at even indices (0, 2, 4, ...): those Polycarp places from the LEFT
ghost function Evens(a: seq<int>): seq<int>
  decreases |a|
{
  if |a| == 0 then []
  else if |a| == 1 then [a[0]]
  else [a[0]] + Evens(a[2..])
}

// Elements at odd indices (1, 3, 5, ...): those Polycarp places from the RIGHT
ghost function Odds(a: seq<int>): seq<int>
{
  if |a| <= 1 then []
  else Evens(a[1..])
}

// Reverse a sequence
ghost function Reverse(a: seq<int>): seq<int>
  decreases |a|
{
  if |a| == 0 then []
  else Reverse(a[1..]) + [a[0]]
}

// Simulate Polycarp's whiteboard writing process:
// He alternately places favorite[0] at the left, favorite[1] at the right,
// favorite[2] next-to-left, favorite[3] next-to-right, etc.
// The left-placed elements (even indices) fill left-to-right,
// and the right-placed elements (odd indices) fill right-to-left,
// so the whiteboard reads: Evens(favorite) ++ Reverse(Odds(favorite)).
ghost function WriteOnWhiteboard(favorite: seq<int>): seq<int>
{
  Evens(favorite) + Reverse(Odds(favorite))
}

// The favorite sequence is valid for a given whiteboard if writing it
// using Polycarp's process reproduces exactly that whiteboard.
ghost predicate IsValidFavoriteSequence(favorite: seq<int>, whiteboard: seq<int>)
{
  |favorite| == |whiteboard| && WriteOnWhiteboard(favorite) == whiteboard
}

// --- Implementation ---

method {:verify false} FavoriteSequence(b: seq<int>) returns (a: seq<int>)
  ensures IsValidFavoriteSequence(a, b)
{
  var x := 1;
  var y := 0;
  a := [];
  var i := 0;
  while i < |b|
  {
    if y == 0 {
      a := a + [b[x - 1]];
      y := 1;
    } else {
      a := a + [b[|b| - x]];
      x := x + 1;
      y := 0;
    }
    i := i + 1;
  }
}
// Minimum Domino Rotations
// Task: Add loop invariants so that Dafny can verify this program.

function Min(a: int, b: int): int { if a <= b then a else b }

// Count rotations needed to make all of 'target' row equal to val
function CountRotations(tops: seq<int>, bottoms: seq<int>, val: int, toTop: bool): int
  requires |tops| == |bottoms|
{
  CountRotationsHelper(tops, bottoms, val, toTop, 0)
}

function CountRotationsHelper(tops: seq<int>, bottoms: seq<int>, val: int, toTop: bool, i: int): int
  requires |tops| == |bottoms|
  requires 0 <= i <= |tops|
  decreases |tops| - i
{
  if i == |tops| then 0
  else if toTop && tops[i] == val then CountRotationsHelper(tops, bottoms, val, toTop, i + 1)
  else if toTop && bottoms[i] == val then 1 + CountRotationsHelper(tops, bottoms, val, toTop, i + 1)
  else if !toTop && bottoms[i] == val then CountRotationsHelper(tops, bottoms, val, toTop, i + 1)
  else if !toTop && tops[i] == val then 1 + CountRotationsHelper(tops, bottoms, val, toTop, i + 1)
  else -1  // impossible sentinel
}

method MinDominoRotations(tops: seq<int>, bottoms: seq<int>) returns (result: int)
  requires |tops| == |bottoms|
  requires |tops| > 0
  ensures result >= -1
{
  result := -1;
  // Try making all tops equal to tops[0] or bottoms[0]
  var candidates := [tops[0], bottoms[0]];
  var c := 0;
  while c < |candidates|
  {
    var val := candidates[c];
    // Count rotations for top row
    var rotTop := 0;
    var possible := true;
    var i := 0;
    while i < |tops|
    {
      if tops[i] == val {
        // no rotation needed
      } else if bottoms[i] == val {
        rotTop := rotTop + 1;
      } else {
        possible := false;
        break;
      }
      i := i + 1;
    }
    if possible && (result == -1 || rotTop < result) {
      result := rotTop;
    }

    // Count rotations for bottom row
    var rotBot := 0;
    possible := true;
    i := 0;
    while i < |tops|
    {
      if bottoms[i] == val {
        // no rotation needed
      } else if tops[i] == val {
        rotBot := rotBot + 1;
      } else {
        possible := false;
        break;
      }
      i := i + 1;
    }
    if possible && (result == -1 || rotBot < result) {
      result := rotBot;
    }
    c := c + 1;
  }
}

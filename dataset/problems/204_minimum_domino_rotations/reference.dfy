// Minimum Domino Rotations -- Reference solution with invariants

function Min(a: int, b: int): int { if a <= b then a else b }

method MinDominoRotations(tops: seq<int>, bottoms: seq<int>) returns (result: int)
  requires |tops| == |bottoms|
  requires |tops| > 0
  ensures result >= -1
{
  result := -1;
  var candidates := [tops[0], bottoms[0]];
  var c := 0;
  while c < |candidates|
    invariant 0 <= c <= |candidates|
    invariant result >= -1
    decreases |candidates| - c
  {
    var val := candidates[c];
    // Top row
    var rotTop := 0;
    var possible := true;
    var i := 0;
    while i < |tops|
      invariant 0 <= i <= |tops|
      invariant rotTop >= 0
      invariant possible ==> rotTop <= i
      decreases |tops| - i
    {
      if tops[i] == val {
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

    // Bottom row
    var rotBot := 0;
    possible := true;
    i := 0;
    while i < |tops|
      invariant 0 <= i <= |tops|
      invariant rotBot >= 0
      invariant possible ==> rotBot <= i
      decreases |tops| - i
    {
      if bottoms[i] == val {
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

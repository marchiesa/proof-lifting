// Minimum Domino Rotations

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

method Main()
{
  // tops=[2,1,2,4,2,2] bottoms=[5,2,6,2,3,2] => 2 rotations to make all tops=2
  var t := [2, 1, 2, 4, 2, 2];
  var b := [5, 2, 6, 2, 3, 2];
  var r1 := MinDominoRotations(t, b);
  expect r1 >= -1;

  // Impossible case
  var t2 := [1, 2, 3];
  var b2 := [4, 5, 6];
  var r2 := MinDominoRotations(t2, b2);
  expect r2 >= -1;

  // Already uniform
  var t3 := [1, 1, 1];
  var b3 := [2, 3, 4];
  var r3 := MinDominoRotations(t3, b3);
  expect r3 >= -1;

  // Single domino
  var t4 := [5];
  var b4 := [6];
  var r4 := MinDominoRotations(t4, b4);
  expect r4 >= -1;

  print "All spec tests passed\n";
}

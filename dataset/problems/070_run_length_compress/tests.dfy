// Run-Length Compress -- Runtime spec tests

// Copy spec functions from task.dfy
function Repeat(v: int, n: nat): seq<int>
  decreases n
{
  if n == 0 then [] else [v] + Repeat(v, n - 1)
}

function Expand(vals: seq<int>, counts: seq<nat>): seq<int>
  requires |vals| == |counts|
  decreases |vals|
{
  if |vals| == 0 then []
  else Repeat(vals[0], counts[0]) + Expand(vals[1..], counts[1..])
}

// Bounded compilable version of NoAdjacentDups
method NoAdjacentDupsCheck(vals: seq<int>) returns (result: bool)
{
  if |vals| <= 1 { return true; }
  var i := 0;
  while i < |vals| - 1
  {
    if vals[i] == vals[i + 1] { return false; }
    i := i + 1;
  }
  return true;
}

// Bounded compilable version of AllPositive
method AllPositiveCheck(counts: seq<nat>) returns (result: bool)
{
  var i := 0;
  while i < |counts|
  {
    if counts[i] == 0 { return false; }
    i := i + 1;
  }
  return true;
}

method Main()
{
  // Test Repeat function
  expect Repeat(3, 0) == [], "Repeat(3,0) should be []";
  expect Repeat(3, 1) == [3], "Repeat(3,1) should be [3]";
  expect Repeat(3, 3) == [3, 3, 3], "Repeat(3,3) should be [3,3,3]";
  expect Repeat(0, 2) == [0, 0], "Repeat(0,2) should be [0,0]";

  // Test Expand function
  expect Expand([], []) == [], "Expand([],[]) should be []";
  expect Expand([1], [3]) == [1, 1, 1], "Expand([1],[3]) should be [1,1,1]";
  expect Expand([1, 2], [2, 3]) == [1, 1, 2, 2, 2], "Expand([1,2],[2,3]) should be [1,1,2,2,2]";
  expect Expand([1, 2, 3], [1, 1, 1]) == [1, 2, 3], "Expand single counts should return vals";

  // Test Expand matches original: [1,1,2,3,3,3]
  expect Expand([1, 2, 3], [2, 1, 3]) == [1, 1, 2, 3, 3, 3],
    "Expand([1,2,3],[2,1,3]) should be [1,1,2,3,3,3]";

  // Test NoAdjacentDups
  var r := NoAdjacentDupsCheck([1, 2, 3]);
  expect r, "[1,2,3] has no adjacent dups";

  r := NoAdjacentDupsCheck([1, 1, 2]);
  expect !r, "[1,1,2] has adjacent dups";

  r := NoAdjacentDupsCheck([]);
  expect r, "[] has no adjacent dups";

  r := NoAdjacentDupsCheck([5]);
  expect r, "[5] has no adjacent dups";

  r := NoAdjacentDupsCheck([1, 2, 1]);
  expect r, "[1,2,1] has no adjacent dups (non-adjacent same values ok)";

  // Test AllPositive
  r := AllPositiveCheck([1, 2, 3]);
  expect r, "[1,2,3] all positive";

  r := AllPositiveCheck([0, 1, 2]);
  expect !r, "[0,1,2] not all positive (0 present)";

  r := AllPositiveCheck([]);
  expect r, "[] vacuously all positive";

  // Negative test: wrong Expand
  expect Expand([1, 2], [2, 3]) != [1, 1, 2, 2], "Wrong count should give wrong result";

  print "All spec tests passed\n";
}

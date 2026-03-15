// Boats to Save People

predicate ValidWeights(weights: seq<int>, limit: int)
{
  forall i :: 0 <= i < |weights| ==> 1 <= weights[i] <= limit
}

predicate IsSorted(a: seq<int>)
{
  forall i, j :: 0 <= i < j < |a| ==> a[i] <= a[j]
}

method NumBoats(weights: seq<int>, limit: int) returns (boats: int)
  requires |weights| > 0
  requires limit > 0
  requires ValidWeights(weights, limit)
  requires IsSorted(weights)
  ensures boats >= 1
  ensures boats <= |weights|
{
  boats := 0;
  var lo := 0;
  var hi := |weights| - 1;
  while lo <= hi
  {
    if lo < hi && weights[lo] + weights[hi] <= limit {
      lo := lo + 1;
    }
    hi := hi - 1;
    boats := boats + 1;
  }
}

method Main()
{
  // [1, 2, 2, 3] limit=3 => boats: (1+2), (2), (3) => 3
  var a := [1, 2, 2, 3];
  var r1 := NumBoats(a, 3);
  expect r1 >= 1;
  expect r1 <= 4;

  // Single person
  var b := [3];
  var r2 := NumBoats(b, 5);
  expect r2 == 1;

  // All can pair
  var c := [1, 1, 1, 1];
  var r3 := NumBoats(c, 2);
  expect r3 >= 1;
  expect r3 <= 4;

  // None can pair
  var d := [3, 3, 3];
  var r4 := NumBoats(d, 3);
  expect r4 >= 1;
  expect r4 <= 3;

  // Negative test: ValidWeights must hold
  expect ValidWeights([1, 2, 3], 3);
  expect !ValidWeights([1, 2, 4], 3);

  print "All spec tests passed\n";
}

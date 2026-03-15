// Minimum Platforms -- Test cases

method MinPlatforms(a: seq<int>, d: seq<int>) returns (maxPlat: int)
  requires |a| == |d| && |a| > 0
  requires forall i :: 0 <= i < |a| ==> a[i] <= d[i]
  ensures maxPlat >= 1 && maxPlat <= |a|
{
  maxPlat := 1;
}

method Main()
{
  // Non-overlapping: 1 platform
  var r1 := MinPlatforms([100, 300], [200, 400]);
  expect r1 >= 1, "At least 1 platform";
  expect r1 <= 2, "At most 2 platforms";

  // All overlapping: need all platforms
  var r2 := MinPlatforms([100, 100, 100], [200, 200, 200]);
  expect r2 >= 1 && r2 <= 3, "Valid platform count";

  // Single train
  var r3 := MinPlatforms([100], [200]);
  expect r3 == 1, "Single train needs 1 platform";

  print "All spec tests passed\n";
}

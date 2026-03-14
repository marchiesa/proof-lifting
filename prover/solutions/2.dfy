predicate HasPair(s: seq<int>, target: int)
{
  exists i, j {:trigger s[i], s[j]} :: 0 <= i < j < |s| && s[i] + s[j] == target
}

predicate AllPositive(s: seq<int>)
{
  forall i :: 0 <= i < |s| ==> s[i] > 0
}

method findPairExists(nums: seq<int>, target: int) returns (found: bool)
  requires |nums| >= 2
  ensures found ==> HasPair(nums, target)
  ensures !found ==> !HasPair(nums, target)
{
  var i := 0;
  found := false;
  while i < |nums|
    invariant 0 <= i <= |nums|
    invariant !found
    invariant forall a, b {:trigger nums[a], nums[b]} :: 0 <= a < i && a < b < |nums| ==> nums[a] + nums[b] != target
  {
    var j := i + 1;
    while j < |nums|
      invariant i + 1 <= j <= |nums|
      invariant forall b {:trigger nums[b]} :: i + 1 <= b < j ==> nums[i] + nums[b] != target
    {
      if nums[i] + nums[j] == target {
        found := true;
        assert nums[i] + nums[j] == target;
        assert 0 <= i < j < |nums|;
        return;
      }
      j := j + 1;
    }
    i := i + 1;
  }
}

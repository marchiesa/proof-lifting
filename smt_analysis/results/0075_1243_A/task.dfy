// --- Specification ---

// Count how many elements in a are >= threshold
ghost function CountAtLeast(a: seq<int>, threshold: int): int
  decreases |a|
{
  if |a| == 0 then 0
  else (if a[|a|-1] >= threshold then 1 else 0) + CountAtLeast(a[..|a|-1], threshold)
}

// A square of side s is achievable iff we can select s planks each of height >= s
ghost predicate IsAchievable(a: seq<int>, s: int)
{
  s >= 0 && CountAtLeast(a, s) >= s
}

// side is the maximum achievable square side length
ghost predicate IsMaxSquareSide(a: seq<int>, side: int)
{
  IsAchievable(a, side) &&
  forall s :: side < s <= |a| ==> !IsAchievable(a, s)
}

// --- Implementation (body unchanged) ---

method {:verify false} MaximumSquare(a: seq<int>) returns (side: int)
  ensures IsMaxSquareSide(a, side)
{
  var n := |a|;
  var arr := new int[n];
  var k := 0;
  while k < n {
    arr[k] := a[k];
    k := k + 1;
  }

  // Sort descending (insertion sort)
  var i := 1;
  while i < n {
    var key := arr[i];
    var j := i - 1;
    while j >= 0 && arr[j] < key {
      arr[j + 1] := arr[j];
      j := j - 1;
    }
    arr[j + 1] := key;
    i := i + 1;
  }

  // Find largest side s where at least s elements >= s
  side := n;
  i := 0;
  while i < n {
    if arr[i] < i + 1 {
      side := i;
      return;
    }
    i := i + 1;
  }

  return;
}
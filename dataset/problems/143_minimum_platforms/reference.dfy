// Minimum Platforms -- Reference solution with invariants

method MinPlatforms(arrivals: seq<int>, departures: seq<int>) returns (maxPlat: int)
  requires |arrivals| == |departures|
  requires |arrivals| > 0
  requires forall i :: 0 <= i < |arrivals| ==> arrivals[i] <= departures[i]
  ensures maxPlat >= 1
  ensures maxPlat <= |arrivals|
{
  maxPlat := 0;
  var i := 0;
  while i < |arrivals|
    invariant 0 <= i <= |arrivals|
    invariant 0 <= maxPlat <= |arrivals|
    invariant i > 0 ==> maxPlat >= 1
    decreases |arrivals| - i
  {
    var count := 0;
    var j := 0;
    ghost var selfCounted := false;
    while j < |arrivals|
      invariant 0 <= j <= |arrivals|
      invariant 0 <= count <= j
      invariant j > i ==> selfCounted
      invariant selfCounted ==> count >= 1
      decreases |arrivals| - j
    {
      if arrivals[j] <= arrivals[i] && arrivals[i] <= departures[j] {
        count := count + 1;
        if j == i {
          selfCounted := true;
        }
      }
      if j == i && !selfCounted {
        assert arrivals[i] <= arrivals[i];
        assert arrivals[i] <= departures[i];
        assert false; // contradiction: the if condition must have been true
      }
      j := j + 1;
    }
    if count > maxPlat {
      maxPlat := count;
    }
    i := i + 1;
  }
}

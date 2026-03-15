// Minimum Platforms (Scheduling)
// Task: Add loop invariants so that Dafny can verify this program.
// Given arrival and departure times, find max number of trains present at once.

function Max(a: int, b: int): int { if a >= b then a else b }

function MaxOverlap(arrivals: seq<int>, departures: seq<int>, time: int): int
  requires |arrivals| == |departures|
{
  CountPresent(arrivals, departures, time, 0)
}

function CountPresent(arr: seq<int>, dep: seq<int>, time: int, idx: int): int
  requires |arr| == |dep|
  requires 0 <= idx <= |arr|
  decreases |arr| - idx
{
  if idx >= |arr| then 0
  else (if arr[idx] <= time && time <= dep[idx] then 1 else 0) +
       CountPresent(arr, dep, time, idx + 1)
}

method MinPlatforms(arrivals: seq<int>, departures: seq<int>) returns (maxPlat: int)
  requires |arrivals| == |departures|
  requires |arrivals| > 0
  requires forall i :: 0 <= i < |arrivals| ==> arrivals[i] <= departures[i]
  ensures maxPlat >= 1
  ensures maxPlat <= |arrivals|
{
  // Brute force: check overlap at every arrival time
  maxPlat := 0;
  var i := 0;
  while i < |arrivals|
  {
    var count := 0;
    var j := 0;
    while j < |arrivals|
    {
      if arrivals[j] <= arrivals[i] && arrivals[i] <= departures[j] {
        count := count + 1;
      }
      j := j + 1;
    }
    if count > maxPlat {
      maxPlat := count;
    }
    i := i + 1;
  }
}

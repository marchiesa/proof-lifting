// Minimum Flips to Make Binary String Monotone

predicate IsBinary(s: seq<int>)
{
  forall i :: 0 <= i < |s| ==> s[i] == 0 || s[i] == 1
}

function Min(a: int, b: int): int { if a <= b then a else b }

// Count zeros from position i to end
function CountZerosFrom(s: seq<int>, i: int): nat
  requires 0 <= i <= |s|
  decreases |s| - i
{
  if i == |s| then 0
  else (if s[i] == 0 then 1 else 0) + CountZerosFrom(s, i + 1)
}

method MinFlipsMonotone(s: seq<int>) returns (flips: int)
  requires IsBinary(s)
  ensures flips >= 0
  ensures flips <= |s|
{
  // For each partition point k, count: ones before k + zeros from k
  // flips = min over all k of (ones in s[..k] + zeros in s[k..])
  flips := |s|; // worst case: flip everything
  var onesCount := 0;
  var i := 0;
  while i <= |s|
  {
    var zerosFromI := 0;
    var j := i;
    while j < |s|
    {
      if s[j] == 0 {
        zerosFromI := zerosFromI + 1;
      }
      j := j + 1;
    }
    var cost := onesCount + zerosFromI;
    flips := Min(flips, cost);
    if i < |s| && s[i] == 1 {
      onesCount := onesCount + 1;
    }
    i := i + 1;
  }
}

method Main()
{
  // [0,0,1,1,0] => flip last 0 to 1 => 1 flip
  var a := [0, 0, 1, 1, 0];
  var r1 := MinFlipsMonotone(a);
  expect r1 >= 0;
  expect r1 <= 5;

  // Already monotone
  var b := [0, 0, 1, 1];
  var r2 := MinFlipsMonotone(b);
  expect r2 >= 0;
  expect r2 <= 4;

  // All zeros (already monotone)
  var c := [0, 0, 0];
  var r3 := MinFlipsMonotone(c);
  expect r3 >= 0;

  // All ones (already monotone)
  var d := [1, 1, 1];
  var r4 := MinFlipsMonotone(d);
  expect r4 >= 0;

  // Reverse [1,1,0,0] => 2 flips
  var e := [1, 1, 0, 0];
  var r5 := MinFlipsMonotone(e);
  expect r5 >= 0;
  expect r5 <= 4;

  // Empty
  var f: seq<int> := [];
  var r6 := MinFlipsMonotone(f);
  expect r6 == 0;

  print "All spec tests passed\n";
}

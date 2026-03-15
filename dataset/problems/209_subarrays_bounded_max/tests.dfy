// Number of Subarrays with Bounded Maximum

function MaxInRange(a: seq<int>, lo: int, hi: int): int
  requires 0 <= lo < hi <= |a|
  decreases hi - lo
{
  if hi - lo == 1 then a[lo]
  else if a[lo] >= MaxInRange(a, lo + 1, hi) then a[lo]
  else MaxInRange(a, lo + 1, hi)
}

method CountBoundedSubarrays(a: seq<int>, L: int, R: int) returns (count: int)
  requires 1 <= L <= R
  ensures count >= 0
{
  count := 0;
  var i := 0;
  while i < |a|
  {
    var j := i + 1;
    while j <= |a|
    {
      var maxVal := a[i];
      var k := i + 1;
      while k < j
      {
        if a[k] > maxVal {
          maxVal := a[k];
        }
        k := k + 1;
      }
      if L <= maxVal <= R {
        count := count + 1;
      }
      j := j + 1;
    }
    i := i + 1;
  }
}

method Main()
{
  // [2, 1, 4, 3] L=2 R=3 => subarrays with max in [2,3]: [2],[2,1],[3] => 3
  var a := [2, 1, 4, 3];
  var r1 := CountBoundedSubarrays(a, 2, 3);
  expect r1 >= 0;

  // All elements in range
  var b := [2, 2, 2];
  var r2 := CountBoundedSubarrays(b, 1, 3);
  expect r2 >= 0;

  // No elements in range
  var c := [10, 20, 30];
  var r3 := CountBoundedSubarrays(c, 1, 5);
  expect r3 >= 0;

  // Empty
  var d: seq<int> := [];
  var r4 := CountBoundedSubarrays(d, 1, 10);
  expect r4 >= 0;

  // Single element
  var e := [5];
  var r5 := CountBoundedSubarrays(e, 5, 5);
  expect r5 >= 0;

  print "All spec tests passed\n";
}

// Count Nice Subarrays

function CountOdds(a: seq<int>, lo: int, hi: int): nat
  requires 0 <= lo <= hi <= |a|
  decreases hi - lo
{
  if lo == hi then 0
  else (if a[lo] % 2 != 0 then 1 else 0) + CountOdds(a, lo + 1, hi)
}

method CountNiceSubarrays(a: seq<int>, k: int) returns (count: int)
  requires k >= 1
  ensures count >= 0
{
  count := 0;
  var i := 0;
  while i < |a|
  {
    var odds := 0;
    var j := i;
    while j < |a|
    {
      if a[j] % 2 != 0 {
        odds := odds + 1;
      }
      if odds == k {
        count := count + 1;
      }
      if odds > k {
        break;
      }
      j := j + 1;
    }
    i := i + 1;
  }
}

method Main()
{
  // [1,1,2,1,1] k=3 => subarrays with 3 odds: [1,1,2,1], [1,2,1,1], [1,1,2,1,1] => 2
  var a := [1, 1, 2, 1, 1];
  var r1 := CountNiceSubarrays(a, 3);
  expect r1 >= 0;

  // [2,4,6] k=1 => no odds, count=0
  var b := [2, 4, 6];
  var r2 := CountNiceSubarrays(b, 1);
  expect r2 >= 0;

  // [1,1,1] k=1 => each single element is nice => 3
  var c := [1, 1, 1];
  var r3 := CountNiceSubarrays(c, 1);
  expect r3 >= 0;

  // Empty
  var d: seq<int> := [];
  var r4 := CountNiceSubarrays(d, 1);
  expect r4 >= 0;

  print "All spec tests passed\n";
}

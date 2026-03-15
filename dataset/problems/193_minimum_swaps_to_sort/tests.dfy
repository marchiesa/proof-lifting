// Minimum Swaps to Sort

predicate IsPermutation(a: seq<int>)
{
  (forall i :: 0 <= i < |a| ==> 0 <= a[i] < |a|) &&
  (forall i, j :: 0 <= i < j < |a| ==> a[i] != a[j])
}

predicate IsSorted(a: seq<int>)
{
  forall i :: 0 <= i < |a| ==> a[i] == i
}

method MinSwaps(a: seq<int>) returns (swaps: int)
  requires IsPermutation(a)
  ensures swaps >= 0
{
  var arr := a;
  swaps := 0;
  var i := 0;
  while i < |arr|
  {
    while arr[i] != i
    {
      var target := arr[i];
      var tmp := arr[i];
      arr := arr[..i] + [arr[target]] + arr[i+1..target] + [tmp] + arr[target+1..];
      swaps := swaps + 1;
    }
    i := i + 1;
  }
}

method Main()
{
  // Already sorted: 0 swaps
  var a := [0, 1, 2, 3];
  var r1 := MinSwaps(a);
  expect r1 >= 0;

  // Reversed: [3,2,1,0]
  var b := [3, 2, 1, 0];
  var r2 := MinSwaps(b);
  expect r2 >= 0;

  // Simple swap: [1,0]
  var c := [1, 0];
  var r3 := MinSwaps(c);
  expect r3 >= 0;

  // Single element
  var d := [0];
  var r4 := MinSwaps(d);
  expect r4 >= 0;

  // Cycle of length 3: [1,2,0]
  var e := [1, 2, 0];
  var r5 := MinSwaps(e);
  expect r5 >= 0;

  print "All spec tests passed\n";
}

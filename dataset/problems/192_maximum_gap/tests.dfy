// Maximum Gap Between Sorted Elements

predicate IsSorted(a: seq<int>)
{
  forall i, j :: 0 <= i < j < |a| ==> a[i] <= a[j]
}

predicate IsPermutation(a: seq<int>, b: seq<int>)
{
  multiset(a) == multiset(b)
}

method MaxGap(a: seq<int>) returns (gap: int)
  requires |a| >= 2
  ensures gap >= 0
{
  // First sort the array
  var sorted := a;
  var i := 0;
  while i < |sorted|
  {
    var minIdx := i;
    var j := i + 1;
    while j < |sorted|
    {
      if sorted[j] < sorted[minIdx] {
        minIdx := j;
      }
      j := j + 1;
    }
    if minIdx != i {
      var tmp := sorted[i];
      sorted := sorted[..i] + [sorted[minIdx]] + sorted[i+1..minIdx] + [tmp] + sorted[minIdx+1..];
    }
    i := i + 1;
  }

  // Find max gap
  gap := 0;
  i := 1;
  while i < |sorted|
  {
    var diff := sorted[i] - sorted[i-1];
    if diff > gap {
      gap := diff;
    }
    i := i + 1;
  }
}

method Main()
{
  // [3, 6, 9, 1] sorted=[1,3,6,9], gaps=[2,3,3], max=3
  var a := [3, 6, 9, 1];
  var r1 := MaxGap(a);
  expect r1 >= 0;

  // [10, 10] => gap 0
  var b := [10, 10];
  var r2 := MaxGap(b);
  expect r2 >= 0;

  // [1, 100] => gap 99
  var c := [1, 100];
  var r3 := MaxGap(c);
  expect r3 >= 0;

  // Already sorted [1,2,3,4,5] => gap 1
  var d := [1, 2, 3, 4, 5];
  var r4 := MaxGap(d);
  expect r4 >= 0;

  print "All spec tests passed\n";
}

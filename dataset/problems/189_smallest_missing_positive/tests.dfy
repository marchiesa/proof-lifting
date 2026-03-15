// Smallest Missing Positive Integer

method SmallestMissing(a: seq<int>) returns (result: int)
  ensures result >= 1
  ensures forall i :: 0 <= i < |a| ==> a[i] != result
  ensures forall w :: 1 <= w < result ==> w in a
{
  result := 1;
  while result <= |a|
  {
    var found := false;
    var j := 0;
    while j < |a|
    {
      if a[j] == result {
        found := true;
        break;
      }
      j := j + 1;
    }
    if !found {
      return;
    }
    result := result + 1;
  }
}

method Main()
{
  // [3, 4, -1, 1] => missing 2
  var a := [3, 4, -1, 1];
  var r1 := SmallestMissing(a);
  expect r1 >= 1;
  expect r1 == 2;

  // [1, 2, 0] => missing 3
  var b := [1, 2, 0];
  var r2 := SmallestMissing(b);
  expect r2 >= 1;
  expect r2 == 3;

  // Empty => missing 1
  var c: seq<int> := [];
  var r3 := SmallestMissing(c);
  expect r3 == 1;

  // [1, 2, 3, 4, 5] => missing 6
  var d := [1, 2, 3, 4, 5];
  var r4 := SmallestMissing(d);
  expect r4 == 6;

  // All negatives => missing 1
  var e := [-3, -2, -1];
  var r5 := SmallestMissing(e);
  expect r5 == 1;

  // Negative test: result is not in array
  expect !(r1 in a);

  print "All spec tests passed\n";
}

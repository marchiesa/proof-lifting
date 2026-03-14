// Count Occurrences -- Test cases

function CountSpec(a: seq<int>, target: int): int
  decreases |a|
{
  if |a| == 0 then 0
  else (if a[0] == target then 1 else 0) + CountSpec(a[1..], target)
}

method {:axiom} CountOccurrences(a: seq<int>, target: int) returns (count: int)
  ensures count == CountSpec(a, target)

method TestMultipleOccurrences()
{
  var a := [1, 3, 5, 3, 3, 7];
  var c := CountOccurrences(a, 3);
  assert CountSpec(a, 3) == 3;
  assert c == 3;
}

method TestNoOccurrences()
{
  var a := [1, 2, 3];
  var c := CountOccurrences(a, 4);
  assert CountSpec(a, 4) == 0;
  assert c == 0;
}

method TestEmpty()
{
  var a: seq<int> := [];
  var c := CountOccurrences(a, 1);
  assert c == 0;
}

method TestAllMatch()
{
  var a := [7, 7, 7];
  var c := CountOccurrences(a, 7);
  assert CountSpec(a, 7) == 3;
  assert c == 3;
}

method TestSingleMatch()
{
  var a := [42];
  var c := CountOccurrences(a, 42);
  assert CountSpec(a, 42) == 1;
  assert c == 1;
}

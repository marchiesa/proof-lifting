// Count Elements Greater Than Threshold -- Test cases

function CountGreater(s: seq<int>, threshold: int): nat
{
  if |s| == 0 then 0
  else (if s[0] > threshold then 1 else 0) + CountGreater(s[1..], threshold)
}

method {:axiom} CountGreaterThan(a: seq<int>, threshold: int) returns (count: nat)
  ensures count == CountGreater(a, threshold)

method TestBasic()
{
  var c := CountGreaterThan([1, 5, 3, 7, 2], 3);
  assert CountGreater([1, 5, 3, 7, 2], 3) == 2;
  assert c == 2;
}

method TestAllGreater()
{
  var c := CountGreaterThan([10, 20, 30], 0);
  assert CountGreater([10, 20, 30], 0) == 3;
  assert c == 3;
}

method TestNoneGreater()
{
  var c := CountGreaterThan([1, 2, 3], 10);
  assert CountGreater([1, 2, 3], 10) == 0;
  assert c == 0;
}

method TestEmpty()
{
  var c := CountGreaterThan([], 5);
  assert c == 0;
}

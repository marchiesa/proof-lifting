method MinColors(a: seq<int>) returns (result: int)
{
  var freq: map<int, int> := map[];
  for i := 0 to |a| {
    var key := a[i];
    if key in freq {
      freq := freq[key := freq[key] + 1];
    } else {
      freq := freq[key := 1];
    }
  }
  result := 0;
  var keys := freq.Keys;
  while keys != {}
    decreases keys
  {
    var k :| k in keys;
    if freq[k] > result {
      result := freq[k];
    }
    keys := keys - {k};
  }
}

method Main()
{
  var r: int;

  r := MinColors([1, 1, 1, 2, 3, 4]);
  expect r == 3, "Test 1a failed";

  r := MinColors([1, 1, 2, 2, 3]);
  expect r == 2, "Test 1b failed";

  r := MinColors([2, 2, 2, 2]);
  expect r == 4, "Test 1c failed";

  r := MinColors([1, 2, 3]);
  expect r == 1, "Test 1d failed";

  r := MinColors([1]);
  expect r == 1, "Test 1e failed";

  r := MinColors([1, 2]);
  expect r == 1, "Test 2b failed";

  r := MinColors([1, 1, 1]);
  expect r == 3, "Test 2c failed";

  r := MinColors([1, 1, 2, 3, 3]);
  expect r == 2, "Test 3 failed";

  r := MinColors([1, 2, 3, 4]);
  expect r == 1, "Test 4a failed";

  r := MinColors([1, 1, 1, 2, 2, 3]);
  expect r == 3, "Test 4b failed";

  r := MinColors([1, 1, 2, 2, 3, 3, 4, 4, 5, 5]);
  expect r == 2, "Test 5 failed";

  r := MinColors([1, 2, 2, 2, 3, 4, 4]);
  expect r == 3, "Test 8 failed";

  r := MinColors([1, 1, 1, 1, 1, 1, 1, 1]);
  expect r == 8, "Test 9 failed";

  r := MinColors([1, 2, 3, 4, 5]);
  expect r == 1, "Test 10a failed";

  r := MinColors([1, 1, 2, 2]);
  expect r == 2, "Test 10b failed";

  r := MinColors([1, 1, 2, 3, 3, 3]);
  expect r == 3, "Test 10c failed";

  r := MinColors([1, 1, 1, 2, 3, 3, 4, 5, 5, 5]);
  expect r == 3, "Test 11 failed";

  print "All tests passed\n";
}
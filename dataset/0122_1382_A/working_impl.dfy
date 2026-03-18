method CommonSubsequence(a: seq<int>, b: seq<int>) returns (found: bool, c: seq<int>)
{
  found := false;
  c := [];
  var i := 0;
  while i < |a|
  {
    var j := 0;
    while j < |b|
    {
      if a[i] == b[j] {
        found := true;
        c := [a[i]];
        return;
      }
      j := j + 1;
    }
    i := i + 1;
  }
}

method Main()
{
  // Test 1, Case 1
  var found1, c1 := CommonSubsequence([10, 8, 6, 4], [1, 2, 3, 4, 5]);
  expect found1 == true;
  expect c1 == [4];

  // Test 1, Case 2
  var found2, c2 := CommonSubsequence([3], [3]);
  expect found2 == true;
  expect c2 == [3];

  // Test 1, Case 3
  var found3, c3 := CommonSubsequence([3], [2]);
  expect found3 == false;

  // Test 1, Case 4
  var found4, c4 := CommonSubsequence([1000, 2, 2, 2, 3], [3, 1, 5]);
  expect found4 == true;
  expect c4 == [3];

  // Test 1, Case 5
  var found5, c5 := CommonSubsequence([1, 2, 3, 4, 5], [1, 2, 3, 4, 5]);
  expect found5 == true;
  expect c5 == [1];

  // Test 2
  var found6, c6 := CommonSubsequence([1, 1], [1, 2, 3]);
  expect found6 == true;
  expect c6 == [1];

  // Test 3
  var found7, c7 := CommonSubsequence([2, 2], [2, 2]);
  expect found7 == true;
  expect c7 == [2];

  // Test 4
  var found8, c8 := CommonSubsequence([1000], [1000]);
  expect found8 == true;
  expect c8 == [1000];

  // Test 5
  var found9, c9 := CommonSubsequence([3], [1, 2, 3]);
  expect found9 == true;
  expect c9 == [3];

  // Test 6
  var found10, c10 := CommonSubsequence([1, 1, 1, 1], [1, 2, 3, 4]);
  expect found10 == true;
  expect c10 == [1];

  // Test 7
  var found11, c11 := CommonSubsequence([1, 1], [1, 2]);
  expect found11 == true;
  expect c11 == [1];

  print "All tests passed\n";
}
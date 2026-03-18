method ReplacingElements(a: seq<int>, d: int) returns (result: bool)
{
  var n := |a|;
  var arr := new int[n];
  var i := 0;
  while i < n {
    arr[i] := a[i];
    i := i + 1;
  }

  // Selection sort
  i := 0;
  while i < n {
    var minIdx := i;
    var j := i + 1;
    while j < n {
      if arr[j] < arr[minIdx] {
        minIdx := j;
      }
      j := j + 1;
    }
    var tmp := arr[i];
    arr[i] := arr[minIdx];
    arr[minIdx] := tmp;
    i := i + 1;
  }

  if n < 2 {
    result := true;
    return;
  }

  if arr[1] > d {
    result := false;
    return;
  }

  i := 2;
  while i < n {
    var m := if arr[0] + arr[1] < arr[i] then arr[0] + arr[1] else arr[i];
    if m > d {
      result := false;
      return;
    }
    i := i + 1;
  }

  result := true;
}

method Main()
{
  // Test 1 (3 cases)
  var r := ReplacingElements([2, 3, 2, 5, 4], 3);
  expect r == false, "Test 1.1 failed: expected NO";

  r := ReplacingElements([2, 4, 4], 4);
  expect r == true, "Test 1.2 failed: expected YES";

  r := ReplacingElements([2, 1, 5, 3, 6], 4);
  expect r == true, "Test 1.3 failed: expected YES";

  // Test 2 (12 cases: all [1,1,1] d=1 → YES)
  var i := 0;
  while i < 12 {
    r := ReplacingElements([1, 1, 1], 1);
    expect r == true, "Test 2 failed";
    i := i + 1;
  }

  // Test 3 (13 cases: all [1,1,1] d=1 → YES)
  i := 0;
  while i < 13 {
    r := ReplacingElements([1, 1, 1], 1);
    expect r == true, "Test 3 failed";
    i := i + 1;
  }

  // Test 4 (11 cases: 3 full cycles of the 3-case pattern + 2 remaining)
  i := 0;
  while i < 3 {
    r := ReplacingElements([2, 3, 2, 5, 4], 3);
    expect r == false, "Test 4 NO failed";
    r := ReplacingElements([2, 4, 4], 4);
    expect r == true, "Test 4 YES(1) failed";
    r := ReplacingElements([2, 1, 5, 3, 6], 4);
    expect r == true, "Test 4 YES(2) failed";
    i := i + 1;
  }
  r := ReplacingElements([2, 3, 2, 5, 4], 3);
  expect r == false, "Test 4.10 failed: expected NO";
  r := ReplacingElements([2, 4, 4], 4);
  expect r == true, "Test 4.11 failed: expected YES";

  // Test 5 (15 cases: all [3,3,3] d=3 → YES)
  i := 0;
  while i < 15 {
    r := ReplacingElements([3, 3, 3], 3);
    expect r == true, "Test 5 failed";
    i := i + 1;
  }

  print "All tests passed\n";
}
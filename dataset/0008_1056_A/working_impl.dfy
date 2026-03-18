method DetermineLine(stops: seq<seq<int>>) returns (result: seq<int>)
{
  if |stops| == 0 { result := []; return; }
  result := stops[0];
  for k := 1 to |stops| {
    var newResult: seq<int> := [];
    for i := 0 to |result| {
      var found := false;
      for j := 0 to |stops[k]| {
        if result[i] == stops[k][j] {
          found := true;
        }
      }
      if found {
        newResult := newResult + [result[i]];
      }
    }
    result := newResult;
  }
}

method SameElements(a: seq<int>, b: seq<int>) returns (same: bool)
{
  if |a| != |b| { return false; }
  for i := 0 to |a| {
    var found := false;
    for j := 0 to |b| {
      if a[i] == b[j] { found := true; }
    }
    if !found { return false; }
  }
  for i := 0 to |b| {
    var found := false;
    for j := 0 to |a| {
      if b[i] == a[j] { found := true; }
    }
    if !found { return false; }
  }
  return true;
}

method Main()
{
  // Test 1
  var r1 := DetermineLine([[1, 4, 6], [1, 4], [10, 5, 6, 4, 1]]);
  var ok1 := SameElements(r1, [1, 4]);
  expect ok1, "Test 1 failed";

  // Test 2
  var r2 := DetermineLine([[1], [10, 9, 8, 7, 100, 5, 4, 3, 99, 1], [1, 2, 3, 4, 5], [4, 1, 3, 2, 5], [10, 1, 5, 3]]);
  var ok2 := SameElements(r2, [1]);
  expect ok2, "Test 2 failed";

  // Test 3
  var r3 := DetermineLine([[100], [2, 100]]);
  var ok3 := SameElements(r3, [100]);
  expect ok3, "Test 3 failed";

  // Test 4
  var r4 := DetermineLine([
    [73, 60, 96, 87, 4, 19],
    [87, 73, 25, 19, 96, 4, 60],
    [19, 60, 87, 4, 25, 96, 73],
    [4, 87, 60, 19, 25, 96],
    [25, 96, 4, 73, 60],
    [25, 4, 60, 73, 87, 96],
    [60, 96, 73, 87, 19, 4],
    [96, 4, 73, 87, 19, 60],
    [4, 73, 87, 96, 19, 60],
    [19, 87, 60, 73, 4, 96]
  ]);
  var ok4 := SameElements(r4, [96, 4, 60]);
  expect ok4, "Test 4 failed";

  // Test 5
  var r5 := DetermineLine([
    [35, 15, 89, 27, 51, 72, 54, 41, 58, 97, 18, 93, 86, 16, 44, 99, 92, 29, 2, 4, 26, 19, 61, 21, 81, 23, 10, 33, 76, 83, 46, 39, 32, 17, 14],
    [90, 55, 28, 52, 56, 84, 9, 30, 25, 29, 73, 40, 77, 42, 95, 13, 6, 75, 96, 24]
  ]);
  var ok5 := SameElements(r5, [29]);
  expect ok5, "Test 5 failed";

  // Test 6
  var r6 := DetermineLine([
    [23, 81, 66, 95, 91, 56, 12, 48, 24, 78, 36, 67, 57, 75, 88, 82, 98, 83, 46, 100, 58, 62, 80, 8, 4, 28, 74, 70, 50, 42, 11, 68, 18, 19, 6, 94, 59, 13, 72, 37, 31, 90, 41, 60, 34, 86, 55, 76, 69, 32, 21, 73, 84, 3, 52, 92, 79, 61, 63, 38, 87, 17, 14, 29],
    [89, 14, 93, 58, 60, 80, 64, 28, 91, 70, 48, 19, 55, 75, 21, 100, 98, 88, 69, 7, 42, 41, 81, 8, 76, 54, 87, 16, 56, 53, 29, 71, 9, 37, 62, 61, 73, 95, 50, 13, 32, 24, 1, 20, 92, 11, 23, 46, 38, 65, 72, 96, 66, 6, 78, 74, 17, 83, 59, 40, 45, 67, 57, 86, 34]
  ]);
  var ok6 := SameElements(r6, [6, 8, 11, 13, 14, 17, 19, 21, 23, 24, 28, 29, 32, 34, 37, 38, 41, 42, 46, 48, 50, 55, 56, 57, 58, 59, 60, 61, 62, 66, 67, 69, 70, 72, 73, 74, 75, 76, 78, 80, 81, 83, 86, 87, 88, 91, 92, 95, 98, 100]);
  expect ok6, "Test 6 failed";

  // Test 7
  var r7 := DetermineLine([[1, 3], [3, 5], [3, 1]]);
  var ok7 := SameElements(r7, [3]);
  expect ok7, "Test 7 failed";

  // Test 8
  var r8 := DetermineLine([[1, 2, 3], [3]]);
  var ok8 := SameElements(r8, [3]);
  expect ok8, "Test 8 failed";

  // Test 9
  var r9 := DetermineLine([[1], [1], [1], [1], [1], [1]]);
  var ok9 := SameElements(r9, [1]);
  expect ok9, "Test 9 failed";

  // Test 10
  var r10 := DetermineLine([[1, 2, 3], [1]]);
  var ok10 := SameElements(r10, [1]);
  expect ok10, "Test 10 failed";

  // Test 11
  var r11 := DetermineLine([[2], [2]]);
  var ok11 := SameElements(r11, [2]);
  expect ok11, "Test 11 failed";

  print "All tests passed\n";
}
method NewYearNaming(n: int, m: int, s: seq<string>, t: seq<string>, queries: seq<int>) returns (results: seq<string>)
{
  results := [];
  for i := 0 to |queries| {
    var x := queries[i] - 1;
    results := results + [s[x % n] + t[x % m]];
  }
}

method Main()
{
  // Test 1
  var r1 := NewYearNaming(10, 12,
    ["sin", "im", "gye", "gap", "eul", "byeong", "jeong", "mu", "gi", "gyeong"],
    ["yu", "sul", "hae", "ja", "chuk", "in", "myo", "jin", "sa", "o", "mi", "sin"],
    [1, 2, 3, 4, 10, 11, 12, 13, 73, 2016, 2017, 2018, 2019, 2020]);
  expect r1 == ["sinyu", "imsul", "gyehae", "gapja", "gyeongo", "sinmi", "imsin", "gyeyu", "gyeyu", "byeongsin", "jeongyu", "musul", "gihae", "gyeongja"], "Test 1 failed";

  // Test 2
  var r2 := NewYearNaming(1, 1, ["a"], ["a"], [1]);
  expect r2 == ["aa"], "Test 2 failed";

  // Test 3
  var r3 := NewYearNaming(10, 12,
    ["sin", "im", "gye", "gap", "eul", "byeong", "jeong", "mu", "gi", "gyeong"],
    ["yu", "sul", "hae", "ja", "chuk", "in", "myo", "jin", "sa", "o", "mi", "sin"],
    [2016]);
  expect r3 == ["byeongsin"], "Test 3 failed";

  // Test 4
  var r4 := NewYearNaming(5, 2, ["a", "b", "c", "d", "e"], ["hola", "mundo"], [5]);
  expect r4 == ["ehola"], "Test 4 failed";

  // Test 5
  var r5 := NewYearNaming(4, 4, ["a", "b", "c", "b"], ["a", "b", "c", "b"], [3]);
  expect r5 == ["cc"], "Test 5 failed";

  // Test 6
  var r6 := NewYearNaming(12, 10,
    ["yu", "sul", "hae", "ja", "chuk", "in", "myo", "jin", "sa", "o", "mi", "sin"],
    ["sin", "im", "gye", "gap", "eul", "byeong", "jeong", "mu", "gi", "gyeong"],
    [1, 2, 3, 4, 10, 11, 12, 13, 73, 2016, 2017, 2018, 2019, 2020]);
  expect r6 == ["yusin", "sulim", "haegye", "jagap", "ogyeong", "misin", "sinim", "yugye", "yugye", "sinbyeong", "yujeong", "sulmu", "haegi", "jagyeong"], "Test 6 failed";

  // Test 7
  var r7 := NewYearNaming(2, 6, ["a", "a"], ["b", "b", "c", "d", "e", "f"], [3]);
  expect r7 == ["ac"], "Test 7 failed";

  print "All tests passed\n";
}
function CyclicIndex(year: int, period: int): int
  requires year >= 1
  requires period > 0
  ensures 0 <= CyclicIndex(year, period) < period
{
  (year - 1) % period
}

function GapjaName(year: int, s: seq<string>, t: seq<string>): string
  requires year >= 1
  requires |s| > 0
  requires |t| > 0
{
  s[CyclicIndex(year, |s|)] + t[CyclicIndex(year, |t|)]
}

method NewYearNaming(n: int, m: int, s: seq<string>, t: seq<string>, queries: seq<int>) returns (results: seq<string>)
  requires n > 0 && m > 0
  requires |s| == n && |t| == m
  requires forall i | 0 <= i < |queries| :: queries[i] >= 1
  ensures |results| == |queries|
  ensures forall i | 0 <= i < |queries| :: results[i] == GapjaName(queries[i], s, t)
{
  results := [];
  for i := 0 to |queries| {
    var x := queries[i] - 1;
    results := results + [s[x % n] + t[x % m]];
  }
}

method Main()
{
  // ===== SPEC POSITIVE TESTS =====
  // Testing GapjaName (top-level ensures predicate) with small inputs

  // SP1: from test 1 (year=1, both indices 0)
  expect GapjaName(1, ["s","i","g"], ["y","s","h"]) == "sy", "spec positive 1";

  // SP2: from test 2 (exact — already small: n=1, m=1)
  expect GapjaName(1, ["a"], ["a"]) == "aa", "spec positive 2";

  // SP3: from test 3 (year=3, n=m=3, wraps to index 2)
  expect GapjaName(3, ["a","b","c"], ["x","y","z"]) == "cz", "spec positive 3";

  // SP4: from test 4 (different n and m: n=3, m=2)
  expect GapjaName(3, ["a","b","c"], ["x","y"]) == "cx", "spec positive 4";

  // SP5: from test 5 (year=3, n=m=3)
  expect GapjaName(3, ["p","q","r"], ["u","v","w"]) == "rw", "spec positive 5";

  // SP6: from test 6 (swapped roles, year=1)
  expect GapjaName(1, ["y","s"], ["s","i"]) == "ys", "spec positive 6";

  // SP7: from test 7 (n=2, m=3, year=3)
  expect GapjaName(3, ["a","a"], ["b","b","c"]) == "ac", "spec positive 7";

  // ===== SPEC NEGATIVE TESTS =====
  // Testing that GapjaName rejects wrong outputs (appended " WRONG")

  // SN1: wrong output for SP1
  expect GapjaName(1, ["s","i","g"], ["y","s","h"]) != "sy WRONG", "spec negative 1";

  // SN2: wrong output for SP2
  expect GapjaName(1, ["a"], ["a"]) != "aa WRONG", "spec negative 2";

  // SN3: wrong output for SP3
  expect GapjaName(3, ["a","b","c"], ["x","y","z"]) != "cz WRONG", "spec negative 3";

  // SN4: wrong output for SP4
  expect GapjaName(3, ["a","b","c"], ["x","y"]) != "cx WRONG", "spec negative 4";

  // SN5: wrong output for SP5
  expect GapjaName(3, ["p","q","r"], ["u","v","w"]) != "rw WRONG", "spec negative 5";

  // SN6: wrong output for SP6
  expect GapjaName(1, ["y","s"], ["s","i"]) != "ys WRONG", "spec negative 6";

  // SN7: wrong output for SP7
  expect GapjaName(3, ["a","a"], ["b","b","c"]) != "ac WRONG", "spec negative 7";

  // ===== IMPLEMENTATION TESTS =====

  // Impl test 1
  var r1 := NewYearNaming(10, 12,
    ["sin", "im", "gye", "gap", "eul", "byeong", "jeong", "mu", "gi", "gyeong"],
    ["yu", "sul", "hae", "ja", "chuk", "in", "myo", "jin", "sa", "o", "mi", "sin"],
    [1, 2, 3, 4, 10, 11, 12, 13, 73, 2016, 2017, 2018, 2019, 2020]);
  expect r1 == ["sinyu", "imsul", "gyehae", "gapja", "gyeongo", "sinmi", "imsin", "gyeyu", "gyeyu", "byeongsin", "jeongyu", "musul", "gihae", "gyeongja"], "impl test 1 failed";

  // Impl test 2
  var r2 := NewYearNaming(1, 1, ["a"], ["a"], [1]);
  expect r2 == ["aa"], "impl test 2 failed";

  // Impl test 3
  var r3 := NewYearNaming(10, 12,
    ["sin", "im", "gye", "gap", "eul", "byeong", "jeong", "mu", "gi", "gyeong"],
    ["yu", "sul", "hae", "ja", "chuk", "in", "myo", "jin", "sa", "o", "mi", "sin"],
    [2016]);
  expect r3 == ["byeongsin"], "impl test 3 failed";

  // Impl test 4
  var r4 := NewYearNaming(5, 2, ["a", "b", "c", "d", "e"], ["hola", "mundo"], [5]);
  expect r4 == ["ehola"], "impl test 4 failed";

  // Impl test 5
  var r5 := NewYearNaming(4, 4, ["a", "b", "c", "b"], ["a", "b", "c", "b"], [3]);
  expect r5 == ["cc"], "impl test 5 failed";

  // Impl test 6
  var r6 := NewYearNaming(12, 10,
    ["yu", "sul", "hae", "ja", "chuk", "in", "myo", "jin", "sa", "o", "mi", "sin"],
    ["sin", "im", "gye", "gap", "eul", "byeong", "jeong", "mu", "gi", "gyeong"],
    [1, 2, 3, 4, 10, 11, 12, 13, 73, 2016, 2017, 2018, 2019, 2020]);
  expect r6 == ["yusin", "sulim", "haegye", "jagap", "ogyeong", "misin", "sinim", "yugye", "yugye", "sinbyeong", "yujeong", "sulmu", "haegi", "jagyeong"], "impl test 6 failed";

  // Impl test 7
  var r7 := NewYearNaming(2, 6, ["a", "a"], ["b", "b", "c", "d", "e", "f"], [3]);
  expect r7 == ["ac"], "impl test 7 failed";

  print "All tests passed\n";
}
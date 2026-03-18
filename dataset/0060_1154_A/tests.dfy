function RemoveIndex(s: seq<int>, m: int): seq<int>
  requires 0 <= m < |s|
  ensures |RemoveIndex(s, m)| == |s| - 1
{
  s[..m] + s[m+1..]
}

predicate IsValidRestoration(x: seq<int>, a: int, b: int, c: int)
{
  |x| == 4 &&
  a > 0 && b > 0 && c > 0 &&
  multiset{a + b, a + c, b + c, a + b + c} == multiset(x)
}

predicate HasValidRestoration(x: seq<int>)
  requires |x| == 4
{
  exists m | 0 <= m < 4 ::
    var rest := RemoveIndex(x, m);
    var a := x[m] - rest[0];
    var b := x[m] - rest[1];
    var c := x[m] - rest[2];
    a > 0 && b > 0 && c > 0 &&
    multiset{a + b, a + c, b + c, a + b + c} == multiset(x)
}

method RestoreThreeNumbers(x: seq<int>) returns (a: int, b: int, c: int)
  requires |x| == 4
  requires HasValidRestoration(x)
  ensures IsValidRestoration(x, a, b, c)
{
  var maxVal := x[0];
  var i := 1;
  while i < |x|
  {
    if x[i] > maxVal {
      maxVal := x[i];
    }
    i := i + 1;
  }

  var result: seq<int> := [];
  i := 0;
  while i < |x|
  {
    if x[i] != maxVal {
      result := result + [maxVal - x[i]];
    }
    i := i + 1;
  }

  a := result[0];
  b := result[1];
  c := result[2];
}

method Main()
{
  // === SPEC POSITIVE TESTS ===
  expect IsValidRestoration([3, 6, 5, 4], 3, 1, 2), "spec positive 1";
  expect IsValidRestoration([40, 40, 40, 60], 20, 20, 20), "spec positive 2";
  expect IsValidRestoration([201, 101, 101, 200], 100, 100, 1), "spec positive 3";
  expect IsValidRestoration([1000000000, 666666667, 666666667, 666666666], 333333333, 333333333, 333333334), "spec positive 4";
  expect IsValidRestoration([600000000, 900000000, 500000000, 1000000000], 400000000, 100000000, 500000000), "spec positive 5";
  expect IsValidRestoration([2, 2, 3, 2], 1, 1, 1), "spec positive 6";
  expect IsValidRestoration([10101000, 101000, 10001000, 10100000], 10000000, 100000, 1000), "spec positive 7";
  expect IsValidRestoration([3, 999999990, 999999991, 999999992], 999999989, 2, 1), "spec positive 8";
  expect IsValidRestoration([500000000, 500000001, 999999999, 1000000000], 500000000, 499999999, 1), "spec positive 9";

  // === SPEC NEGATIVE TESTS ===
  expect !IsValidRestoration([3, 6, 5, 4], 4, 1, 2), "spec negative 1";
  expect !IsValidRestoration([40, 40, 40, 60], 21, 20, 20), "spec negative 2";
  expect !IsValidRestoration([201, 101, 101, 200], 101, 100, 1), "spec negative 3";
  expect !IsValidRestoration([1000000000, 666666667, 666666667, 666666666], 333333334, 333333333, 333333334), "spec negative 4";
  expect !IsValidRestoration([600000000, 900000000, 500000000, 1000000000], 400000001, 100000000, 500000000), "spec negative 5";
  expect !IsValidRestoration([2, 2, 3, 2], 2, 1, 1), "spec negative 6";
  expect !IsValidRestoration([10101000, 101000, 10001000, 10100000], 10000001, 100000, 1000), "spec negative 7";
  expect !IsValidRestoration([3, 999999990, 999999991, 999999992], 999999990, 2, 1), "spec negative 8";
  expect !IsValidRestoration([500000000, 500000001, 999999999, 1000000000], 500000001, 499999999, 1), "spec negative 9";

  // === IMPLEMENTATION TESTS ===
  var a1, b1, c1 := RestoreThreeNumbers([3, 6, 5, 4]);
  expect a1 == 3, "impl test 1 failed: a";
  expect b1 == 1, "impl test 1 failed: b";
  expect c1 == 2, "impl test 1 failed: c";

  var a2, b2, c2 := RestoreThreeNumbers([40, 40, 40, 60]);
  expect a2 == 20, "impl test 2 failed: a";
  expect b2 == 20, "impl test 2 failed: b";
  expect c2 == 20, "impl test 2 failed: c";

  var a3, b3, c3 := RestoreThreeNumbers([201, 101, 101, 200]);
  expect a3 == 100, "impl test 3 failed: a";
  expect b3 == 100, "impl test 3 failed: b";
  expect c3 == 1, "impl test 3 failed: c";

  var a4, b4, c4 := RestoreThreeNumbers([1000000000, 666666667, 666666667, 666666666]);
  expect a4 == 333333333, "impl test 4 failed: a";
  expect b4 == 333333333, "impl test 4 failed: b";
  expect c4 == 333333334, "impl test 4 failed: c";

  var a5, b5, c5 := RestoreThreeNumbers([600000000, 900000000, 500000000, 1000000000]);
  expect a5 == 400000000, "impl test 5 failed: a";
  expect b5 == 100000000, "impl test 5 failed: b";
  expect c5 == 500000000, "impl test 5 failed: c";

  var a6, b6, c6 := RestoreThreeNumbers([2, 2, 3, 2]);
  expect a6 == 1, "impl test 6 failed: a";
  expect b6 == 1, "impl test 6 failed: b";
  expect c6 == 1, "impl test 6 failed: c";

  var a7, b7, c7 := RestoreThreeNumbers([10101000, 101000, 10001000, 10100000]);
  expect a7 == 10000000, "impl test 7 failed: a";
  expect b7 == 100000, "impl test 7 failed: b";
  expect c7 == 1000, "impl test 7 failed: c";

  var a8, b8, c8 := RestoreThreeNumbers([3, 999999990, 999999991, 999999992]);
  expect a8 == 999999989, "impl test 8 failed: a";
  expect b8 == 2, "impl test 8 failed: b";
  expect c8 == 1, "impl test 8 failed: c";

  var a9, b9, c9 := RestoreThreeNumbers([500000000, 500000001, 999999999, 1000000000]);
  expect a9 == 500000000, "impl test 9 failed: a";
  expect b9 == 499999999, "impl test 9 failed: b";
  expect c9 == 1, "impl test 9 failed: c";

  print "All tests passed\n";
}
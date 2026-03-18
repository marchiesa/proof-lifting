predicate InSeq(x: int, s: seq<int>)
{
  exists i | 0 <= i < |s| :: s[i] == x
}

predicate PossibleLine(line: int, stops: seq<seq<int>>)
{
  forall k | 0 <= k < |stops| :: InSeq(line, stops[k])
}

// Combined ensures predicate: soundness + completeness
predicate IsValidResult(stops: seq<seq<int>>, result: seq<int>)
{
  (forall i | 0 <= i < |result| :: PossibleLine(result[i], stops)) &&
  (forall k | 0 <= k < |stops| :: forall j | 0 <= j < |stops[k]| ::
    PossibleLine(stops[k][j], stops) ==> InSeq(stops[k][j], result))
}

method DetermineLine(stops: seq<seq<int>>) returns (result: seq<int>)
  ensures forall i | 0 <= i < |result| :: PossibleLine(result[i], stops)
  ensures forall k | 0 <= k < |stops| :: forall j | 0 <= j < |stops[k]| ::
            PossibleLine(stops[k][j], stops) ==> InSeq(stops[k][j], result)
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
  // ========== SPEC POSITIVE TESTS ==========
  // Small inputs where the correct output satisfies both ensures clauses

  // Scaled from test 1: [[1,4,6],[1,4],[4,1]] -> [1,4]
  expect IsValidResult([[1, 2], [1, 2], [2, 1]], [1, 2]), "spec positive 1";

  // Scaled from test 2: [[1],[1,2],[1,2,3]] -> [1]
  expect IsValidResult([[1], [1, 2], [1, 2, 3]], [1]), "spec positive 2";

  // Scaled from test 3: [[3],[2,3]] -> [3]
  expect IsValidResult([[3], [2, 3]], [3]), "spec positive 3";

  // Test 7 (already small): [[1,3],[3,5],[3,1]] -> [3]
  expect IsValidResult([[1, 3], [3, 5], [3, 1]], [3]), "spec positive 4";

  // Test 8 (already small): [[1,2,3],[3]] -> [3]
  expect IsValidResult([[1, 2, 3], [3]], [3]), "spec positive 5";

  // Test 10 (already small): [[1,2,3],[1]] -> [1]
  expect IsValidResult([[1, 2, 3], [1]], [1]), "spec positive 6";

  // Test 11 (already small): [[2],[2]] -> [2]
  expect IsValidResult([[2], [2]], [2]), "spec positive 7";

  // Scaled from test 9: [[1],[1],[1]] -> [1]
  expect IsValidResult([[1], [1], [1]], [1]), "spec positive 8";

  // ========== SPEC NEGATIVE TESTS ==========
  // Small inputs where the wrong output must NOT satisfy the ensures clauses

  // Scaled neg 1: wrong [0,2] instead of [1,2] — 0 is not a possible line (soundness fail)
  expect !IsValidResult([[1, 2], [1, 2], [2, 1]], [0, 2]), "spec negative 1";

  // Scaled neg 2: wrong [2] instead of [1] — 2 not in [1] (soundness fail)
  expect !IsValidResult([[1], [1, 2], [1, 2, 3]], [2]), "spec negative 2";

  // Scaled neg 3: wrong [4] instead of [3] — 4 not in any stop (soundness fail)
  expect !IsValidResult([[3], [2, 3]], [4]), "spec negative 3";

  // Neg 7 (already small): wrong [4] instead of [3]
  expect !IsValidResult([[1, 3], [3, 5], [3, 1]], [4]), "spec negative 4";

  // Neg 8 (already small): wrong [4] instead of [3]
  expect !IsValidResult([[1, 2, 3], [3]], [4]), "spec negative 5";

  // Neg 10 (already small): wrong [2] instead of [1] — 2 not in [1] (soundness fail)
  expect !IsValidResult([[1, 2, 3], [1]], [2]), "spec negative 6";

  // Scaled neg 9: wrong [2] instead of [1]
  expect !IsValidResult([[1], [1], [1]], [2]), "spec negative 7";

  // Completeness violation: [1] missing possible line 2 from [[1,2],[1,2]]
  expect !IsValidResult([[1, 2], [1, 2]], [1]), "spec negative 8";

  // ========== IMPLEMENTATION TESTS ==========

  // Impl test 1
  var r1 := DetermineLine([[1, 4, 6], [1, 4], [10, 5, 6, 4, 1]]);
  var ok1 := SameElements(r1, [1, 4]);
  expect ok1, "impl test 1 failed";

  // Impl test 2
  var r2 := DetermineLine([[1], [10, 9, 8, 7, 100, 5, 4, 3, 99, 1], [1, 2, 3, 4, 5], [4, 1, 3, 2, 5], [10, 1, 5, 3]]);
  var ok2 := SameElements(r2, [1]);
  expect ok2, "impl test 2 failed";

  // Impl test 3
  var r3 := DetermineLine([[100], [2, 100]]);
  var ok3 := SameElements(r3, [100]);
  expect ok3, "impl test 3 failed";

  // Impl test 4
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
  expect ok4, "impl test 4 failed";

  // Impl test 5
  var r5 := DetermineLine([
    [35, 15, 89, 27, 51, 72, 54, 41, 58, 97, 18, 93, 86, 16, 44, 99, 92, 29, 2, 4, 26, 19, 61, 21, 81, 23, 10, 33, 76, 83, 46, 39, 32, 17, 14],
    [90, 55, 28, 52, 56, 84, 9, 30, 25, 29, 73, 40, 77, 42, 95, 13, 6, 75, 96, 24]
  ]);
  var ok5 := SameElements(r5, [29]);
  expect ok5, "impl test 5 failed";

  // Impl test 6
  var r6 := DetermineLine([
    [23, 81, 66, 95, 91, 56, 12, 48, 24, 78, 36, 67, 57, 75, 88, 82, 98, 83, 46, 100, 58, 62, 80, 8, 4, 28, 74, 70, 50, 42, 11, 68, 18, 19, 6, 94, 59, 13, 72, 37, 31, 90, 41, 60, 34, 86, 55, 76, 69, 32, 21, 73, 84, 3, 52, 92, 79, 61, 63, 38, 87, 17, 14, 29],
    [89, 14, 93, 58, 60, 80, 64, 28, 91, 70, 48, 19, 55, 75, 21, 100, 98, 88, 69, 7, 42, 41, 81, 8, 76, 54, 87, 16, 56, 53, 29, 71, 9, 37, 62, 61, 73, 95, 50, 13, 32, 24, 1, 20, 92, 11, 23, 46, 38, 65, 72, 96, 66, 6, 78, 74, 17, 83, 59, 40, 45, 67, 57, 86, 34]
  ]);
  var ok6 := SameElements(r6, [6, 8, 11, 13, 14, 17, 19, 21, 23, 24, 28, 29, 32, 34, 37, 38, 41, 42, 46, 48, 50, 55, 56, 57, 58, 59, 60, 61, 62, 66, 67, 69, 70, 72, 73, 74, 75, 76, 78, 80, 81, 83, 86, 87, 88, 91, 92, 95, 98, 100]);
  expect ok6, "impl test 6 failed";

  // Impl test 7
  var r7 := DetermineLine([[1, 3], [3, 5], [3, 1]]);
  var ok7 := SameElements(r7, [3]);
  expect ok7, "impl test 7 failed";

  // Impl test 8
  var r8 := DetermineLine([[1, 2, 3], [3]]);
  var ok8 := SameElements(r8, [3]);
  expect ok8, "impl test 8 failed";

  // Impl test 9
  var r9 := DetermineLine([[1], [1], [1], [1], [1], [1]]);
  var ok9 := SameElements(r9, [1]);
  expect ok9, "impl test 9 failed";

  // Impl test 10
  var r10 := DetermineLine([[1, 2, 3], [1]]);
  var ok10 := SameElements(r10, [1]);
  expect ok10, "impl test 10 failed";

  // Impl test 11
  var r11 := DetermineLine([[2], [2]]);
  var ok11 := SameElements(r11, [2]);
  expect ok11, "impl test 11 failed";

  print "All tests passed\n";
}
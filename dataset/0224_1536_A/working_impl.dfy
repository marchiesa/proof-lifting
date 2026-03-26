method Solve(a: seq<int>) returns (possible: bool, b: seq<int>)
  decreases *
{
  if |a| == 0 {
    possible := true;
    b := [];
    return;
  }

  var mx := a[0];
  for k := 1 to |a| {
    if a[k] > mx { mx := a[k]; }
  }

  b := a;
  var seen: set<int> := {};
  for k := 0 to |a| {
    seen := seen + {a[k]};
  }

  var i := 0;
  while i < |b|
    decreases *
  {
    var j := 0;
    while j < |b|
      decreases *
    {
      var d := Abs(b[i] - b[j]);
      if d > mx {
        possible := false;
        b := [];
        return;
      }
      if d !in seen {
        b := b + [d];
        seen := seen + {d};
      }
      j := j + 1;
    }
    i := i + 1;
  }

  possible := true;
}

method Abs(x: int) returns (r: int)
{
  if x < 0 { r := -x; } else { r := x; }
}

method SeqToSet(s: seq<int>) returns (r: set<int>)
{
  r := {};
  for i := 0 to |s| {
    r := r + {s[i]};
  }
}

method CheckYes(a: seq<int>, lbl: string)
  decreases *
{
  var possible, b := Solve(a);
  expect possible, lbl + ": expected YES";
  var bSet := SeqToSet(b);
  // All elements of a must appear in b
  for i := 0 to |a| {
    expect a[i] in bSet, lbl + ": b missing element of a";
  }
  // All elements of b must be distinct
  var seen: set<int> := {};
  for i := 0 to |b| {
    expect b[i] !in seen, lbl + ": duplicate in b";
    seen := seen + {b[i]};
  }
  // Nice property: for every pair, |bi - bj| is in b
  for i := 0 to |b| {
    for j := i + 1 to |b| {
      var d := Abs(b[i] - b[j]);
      expect d in bSet, lbl + ": not nice";
    }
  }
}

method CheckNo(a: seq<int>, lbl: string)
  decreases *
{
  var possible, b := Solve(a);
  expect !possible, lbl + ": expected NO";
}

method Main()
  decreases *
{
  // === Test 1 ===
  CheckYes([3, 0, 9], "T1.1");
  CheckYes([3, 4], "T1.2");
  CheckNo([-7, 3, 13, -2, 8], "T1.3");
  CheckYes([4, 8, 12, 6], "T1.4");

  // === Test 2 ===
  CheckYes([3, 0, 100], "T2.1");
  CheckYes([3, 2, 4, 8], "T2.2");
  CheckYes([24, 31, 47, 83, 21, 7, 63, 26, 48, 49, 44, 76, 55, 18, 84, 14, 82, 93, 37, 88, 28, 61, 9, 8, 0, 10, 23, 66, 36, 2, 97, 71, 39, 98, 87, 30, 52, 81, 94, 5, 86, 35, 75, 13, 96, 22, 59, 19, 53, 99, 73, 4, 95, 17, 41, 43, 85, 74, 60, 72, 50, 15, 79, 45, 25, 90, 27, 58, 77, 42, 65, 69, 56, 54, 3, 16, 33, 20, 67, 46, 34, 40, 68, 62, 78, 38, 1, 92, 32, 12, 80, 57, 64, 11, 29, 91, 70, 6, 89, 51], "T2.3");
  CheckNo([-1, -2], "T2.4");
  CheckNo([5, 4, 3, 2, 0, -1], "T2.5");

  // === Test 3 ===
  CheckNo([-28, -70, -14, -56, 98, 70, 56], "T3.1");
  CheckYes([28, 56, 98], "T3.2");
  CheckNo([56, -56, 98, 14, 28, 0, 70, -42, -84, 42], "T3.3");
  CheckNo([-42, -84, -70, -14], "T3.4");
  CheckNo([14, -56, 42, 28, -84, -42, -14], "T3.5");
  CheckNo([-70, 84], "T3.6");

  // === Test 4 ===
  CheckNo([100, -100, 0, 50], "T4.1");
  CheckNo([50, 0, -50], "T4.2");
  CheckNo([-50, 100, -100, 0, 50], "T4.3");
  CheckNo([100, -100, 0, 50, -50], "T4.4");
  CheckNo([100, -100, 0, 50], "T4.5");

  // === Test 5 ===
  CheckYes([18, 83], "T5.1");
  CheckNo([-95, 0, 95], "T5.2");
  CheckYes([76, 85], "T5.3");
  CheckYes([10, 22], "T5.4");
  CheckYes([51, 66, 11], "T5.5");
  CheckYes([99, 39, 87], "T5.6");
  CheckYes([48, 46], "T5.7");
  CheckYes([56, 2], "T5.8");
  CheckNo([73, 76, -11], "T5.9");
  CheckNo([14, -34, 87], "T5.10");
  CheckYes([83, 31, 10], "T5.11");
  CheckNo([97, 28, -96], "T5.12");
  CheckNo([-19, -99], "T5.13");
  CheckYes([64, 25, 95], "T5.14");
  CheckYes([56, 21, 14], "T5.15");
  CheckYes([61, 75], "T5.16");
  CheckYes([95, 21], "T5.17");
  CheckYes([78, 72], "T5.18");
  CheckNo([-97, 99], "T5.19");
  CheckNo([9, 55, -54], "T5.20");
  CheckNo([16, -48], "T5.21");
  CheckYes([84, 45, 76], "T5.22");
  CheckYes([23, 78], "T5.23");
  CheckYes([86, 90, 24], "T5.24");
  CheckYes([72, 49], "T5.25");
  CheckYes([8, 32, 58], "T5.26");
  CheckYes([65, 10, 23], "T5.27");
  CheckYes([92, 33], "T5.28");
  CheckYes([97, 22, 47], "T5.29");
  CheckNo([-24, 27, 58], "T5.30");
  CheckYes([49, 83], "T5.31");
  CheckYes([57, 33, 22], "T5.32");
  CheckNo([-9, -98], "T5.33");
  CheckYes([2, 19, 7], "T5.34");
  CheckNo([66, -57], "T5.35");
  CheckYes([85, 10], "T5.36");
  CheckYes([36, 39, 81], "T5.37");
  CheckYes([47, 55], "T5.38");
  CheckYes([46, 13, 89], "T5.39");
  CheckNo([71, 47, -20], "T5.40");

  // === Test 6: 50 cases of [-1, 0] -> NO ===
  for i := 0 to 50 {
    CheckNo([-1, 0], "T6");
  }

  // === Test 7: 50 cases of [-1, k] for k=0..49 -> NO ===
  for k := 0 to 50 {
    CheckNo([-1, k], "T7");
  }

  print "All tests passed\n";
}
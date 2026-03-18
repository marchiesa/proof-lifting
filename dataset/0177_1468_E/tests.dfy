// --- Specification ---

function Min2(x: int, y: int): int {
  if x <= y then x else y
}

function ComplementPair(horizI: int, horizJ: int): (int, int)
  requires 0 <= horizI < horizJ < 4
{
  if horizI == 0 && horizJ == 1 then (2, 3)
  else if horizI == 0 && horizJ == 2 then (1, 3)
  else if horizI == 0 && horizJ == 3 then (1, 2)
  else if horizI == 1 && horizJ == 2 then (0, 3)
  else if horizI == 1 && horizJ == 3 then (0, 2)
  else (0, 1)
}

function RectWidth(a: seq<int>, horizI: int, horizJ: int): int
  requires |a| == 4
  requires 0 <= horizI < horizJ < 4
{
  Min2(a[horizI], a[horizJ])
}

function RectHeight(a: seq<int>, horizI: int, horizJ: int): int
  requires |a| == 4
  requires 0 <= horizI < horizJ < 4
{
  var vp := ComplementPair(horizI, horizJ);
  Min2(a[vp.0], a[vp.1])
}

function AssignmentArea(a: seq<int>, horizI: int, horizJ: int): int
  requires |a| == 4
  requires 0 <= horizI < horizJ < 4
{
  RectWidth(a, horizI, horizJ) * RectHeight(a, horizI, horizJ)
}

predicate IsOptimalArea(a: seq<int>, area: int)
  requires |a| == 4
{
  (exists i | 0 <= i < 4 :: exists j | i + 1 <= j < 4 ::
    area == AssignmentArea(a, i, j))
  &&
  (forall i | 0 <= i < 4 :: forall j | i + 1 <= j < 4 ::
    area >= AssignmentArea(a, i, j))
}

// --- Implementation ---

method FourSegments(a: seq<int>) returns (area: int)
  requires |a| == 4
  requires forall i | 0 <= i < 4 :: a[i] > 0
  ensures IsOptimalArea(a, area)
{
  var maxVal := a[0];
  var maxIdx := 0;
  var i := 1;
  while i < |a|
  {
    if a[i] > maxVal {
      maxVal := a[i];
      maxIdx := i;
    }
    i := i + 1;
  }

  var remaining: seq<int> := [];
  i := 0;
  while i < |a|
  {
    if i != maxIdx {
      remaining := remaining + [a[i]];
    }
    i := i + 1;
  }

  var lo := remaining[0];
  var hi := remaining[0];
  i := 1;
  while i < |remaining|
  {
    if remaining[i] < lo {
      lo := remaining[i];
    }
    if remaining[i] > hi {
      hi := remaining[i];
    }
    i := i + 1;
  }

  area := lo * hi;
  return;
}

method Main()
{
  // === SPEC POSITIVE tests (small values, top-level predicate) ===
  expect IsOptimalArea([1, 1, 1, 1], 1), "spec positive 1";
  expect IsOptimalArea([1, 2, 1, 2], 2), "spec positive 2";
  expect IsOptimalArea([2, 3, 2, 3], 6), "spec positive 3";
  expect IsOptimalArea([2, 2, 2, 2], 4), "spec positive 4";
  expect IsOptimalArea([1, 2, 3, 4], 3), "spec positive 5";
  expect IsOptimalArea([3, 1, 4, 1], 3), "spec positive 6";
  expect IsOptimalArea([5, 1, 5, 1], 5), "spec positive 7";
  expect IsOptimalArea([5, 5, 5, 5], 25), "spec positive 8";
  expect IsOptimalArea([2, 3, 4, 5], 8), "spec positive 9";
  expect IsOptimalArea([3, 4, 3, 4], 12), "spec positive 10";

  // === SPEC NEGATIVE tests (small values, wrong outputs must be rejected) ===
  expect !IsOptimalArea([1, 2, 3, 4], 4), "spec negative 1";   // correct: 3
  expect !IsOptimalArea([1, 1, 1, 1], 2), "spec negative 2";   // correct: 1
  expect !IsOptimalArea([2, 3, 2, 3], 7), "spec negative 3";   // correct: 6
  expect !IsOptimalArea([5, 5, 5, 5], 26), "spec negative 4";  // correct: 25
  expect !IsOptimalArea([1, 2, 1, 2], 3), "spec negative 5";   // correct: 2
  expect !IsOptimalArea([2, 3, 4, 5], 9), "spec negative 6";   // correct: 8
  expect !IsOptimalArea([1, 5, 1, 5], 6), "spec negative 7";   // correct: 5
  expect !IsOptimalArea([1, 1, 5, 5], 6), "spec negative 8";   // correct: 5
  expect !IsOptimalArea([3, 4, 3, 4], 13), "spec negative 9";  // correct: 12
  expect !IsOptimalArea([2, 2, 2, 2], 5), "spec negative 10";  // correct: 4

  // === IMPLEMENTATION tests (full-size inputs) ===
  // Test 1
  var r1 := FourSegments([1, 2, 3, 4]);
  expect r1 == 3, "impl test 1.1 failed";
  var r2 := FourSegments([5, 5, 5, 5]);
  expect r2 == 25, "impl test 1.2 failed";
  var r3 := FourSegments([3, 1, 4, 1]);
  expect r3 == 3, "impl test 1.3 failed";
  var r4 := FourSegments([100, 20, 20, 100]);
  expect r4 == 2000, "impl test 1.4 failed";

  // Test 2
  var r5 := FourSegments([1, 1, 1, 1]);
  expect r5 == 1, "impl test 2 failed";

  // Test 3
  var r6 := FourSegments([2, 3, 2, 3]);
  expect r6 == 6, "impl test 3 failed";

  // Test 4
  var r7 := FourSegments([5, 5, 5, 5]);
  expect r7 == 25, "impl test 4 failed";

  // Test 5
  var r8 := FourSegments([1, 2, 1, 2]);
  expect r8 == 2, "impl test 5 failed";

  // Test 6
  var r9 := FourSegments([1, 1, 1, 1]);
  expect r9 == 1, "impl test 6.1 failed";
  var r10 := FourSegments([2, 3, 4, 5]);
  expect r10 == 8, "impl test 6.2 failed";
  var r11 := FourSegments([10, 10, 10, 10]);
  expect r11 == 100, "impl test 6.3 failed";

  // Test 7
  var r12 := FourSegments([1, 50, 1, 50]);
  expect r12 == 50, "impl test 7.1 failed";
  var r13 := FourSegments([7, 3, 7, 3]);
  expect r13 == 21, "impl test 7.2 failed";

  // Test 8
  var r14 := FourSegments([1, 1, 50, 50]);
  expect r14 == 50, "impl test 8 failed";

  // Test 9
  var r15 := FourSegments([3, 4, 3, 4]);
  expect r15 == 12, "impl test 9.1 failed";
  var r16 := FourSegments([1, 2, 3, 4]);
  expect r16 == 3, "impl test 9.2 failed";
  var r17 := FourSegments([5, 1, 5, 1]);
  expect r17 == 5, "impl test 9.3 failed";
  var r18 := FourSegments([10, 20, 10, 20]);
  expect r18 == 200, "impl test 9.4 failed";
  var r19 := FourSegments([2, 2, 2, 2]);
  expect r19 == 4, "impl test 9.5 failed";

  // Test 10
  var r20 := FourSegments([50, 50, 50, 50]);
  expect r20 == 2500, "impl test 10 failed";

  // Test 11
  var r21 := FourSegments([1, 1, 1, 50]);
  expect r21 == 1, "impl test 11.1 failed";
  var r22 := FourSegments([25, 25, 25, 25]);
  expect r22 == 625, "impl test 11.2 failed";

  print "All tests passed\n";
}
// ── Specification: Alexey and Train ──

predicate ValidInput(n: int, schedule: seq<(int, int)>, tm: seq<int>)
{
  n >= 1 &&
  |schedule| == n &&
  |tm| == n &&
  (forall i | 0 <= i < n :: schedule[i].0 < schedule[i].1) &&
  (forall i | 0 <= i < n :: tm[i] >= 0) &&
  (forall i | 1 <= i < n :: schedule[i - 1].1 < schedule[i].0)
}

function CeilDiv2(a: int): int
{
  (a + 1) / 2
}

function ArrivalTime(schedule: seq<(int, int)>, tm: seq<int>): int
  requires |schedule| > 0
  requires |tm| == |schedule|
  decreases |schedule|, 0
{
  var n := |schedule|;
  var prevB := if n == 1 then 0 else schedule[n - 2].1;
  var travelTime := schedule[n - 1].0 - prevB + tm[n - 1];
  if n == 1 then
    travelTime
  else
    DepartureTime(schedule[..n - 1], tm[..n - 1]) + travelTime
}

function DepartureTime(schedule: seq<(int, int)>, tm: seq<int>): int
  requires |schedule| > 0
  requires |tm| == |schedule|
  decreases |schedule|, 1
{
  var arrival := ArrivalTime(schedule, tm);
  var n := |schedule|;
  var ai := schedule[n - 1].0;
  var bi := schedule[n - 1].1;
  var minWait := CeilDiv2(bi - ai);
  var earliestDepart := arrival + minWait;
  if earliestDepart >= bi then earliestDepart else bi
}

// ── Implementation ──

method AlexeyAndTrain(n: int, schedule: seq<(int, int)>, tm: seq<int>) returns (arrivalTime: int)
  requires ValidInput(n, schedule, tm)
  ensures arrivalTime == ArrivalTime(schedule, tm)
{
  var currentTime := 0;
  var prevB := 0;
  var i := 0;
  while i < n
  {
    var ai := schedule[i].0;
    var bi := schedule[i].1;
    var travelTime := ai - prevB + tm[i];
    currentTime := currentTime + travelTime;
    if i < n - 1 {
      var waitTime := bi - ai;
      currentTime := currentTime + (waitTime + 1) / 2;
      if currentTime < bi {
        currentTime := bi;
      }
    }
    prevB := bi;
    i := i + 1;
  }
  arrivalTime := currentTime;
}

method Main()
{
  // ═══════════════════════════════════════════════════
  // SPEC POSITIVE tests (ArrivalTime == correct output)
  // Small inputs only (n <= 3)
  // ═══════════════════════════════════════════════════

  // From Test 1 case 1: n=2
  expect ArrivalTime([(2,4),(10,12)], [0,2]) == 12, "spec positive 1.1";

  // From Test 2: n=1
  expect ArrivalTime([(1,8)], [0]) == 1, "spec positive 2";

  // From Test 3: n=1
  expect ArrivalTime([(1,2)], [0]) == 1, "spec positive 3";

  // From Test 4: n=1
  expect ArrivalTime([(3,5)], [4]) == 7, "spec positive 4";

  // From Test 5: n=2
  expect ArrivalTime([(2,4),(10,12)], [0,2]) == 12, "spec positive 5";

  // From Test 6: n=3
  expect ArrivalTime([(1,3),(5,7),(9,11)], [0,0,0]) == 9, "spec positive 6";

  // From Test 7: n=3
  expect ArrivalTime([(2,4),(6,8),(10,12)], [1,1,1]) == 11, "spec positive 7";

  // From Test 8 case 1: n=1
  expect ArrivalTime([(1,2)], [0]) == 1, "spec positive 8.1";

  // From Test 8 case 2: n=1
  expect ArrivalTime([(5,10)], [3]) == 8, "spec positive 8.2";

  // From Test 10 case 1: n=1
  expect ArrivalTime([(1,3)], [0]) == 1, "spec positive 10.1";

  // From Test 10 case 2: n=2
  expect ArrivalTime([(1,2),(5,8)], [1,0]) == 6, "spec positive 10.2";

  // From Test 10 case 3: n=1
  expect ArrivalTime([(10,20)], [5]) == 15, "spec positive 10.3";

  // ═══════════════════════════════════════════════════
  // SPEC NEGATIVE tests (ArrivalTime != wrong output)
  // Small inputs only (n <= 3)
  // ═══════════════════════════════════════════════════

  // From Neg 1 case 1: n=2, wrong=13
  expect ArrivalTime([(2,4),(10,12)], [0,2]) != 13, "spec negative 1";

  // From Neg 2: n=1, wrong=2
  expect ArrivalTime([(1,8)], [0]) != 2, "spec negative 2";

  // From Neg 3: n=1, wrong=2
  expect ArrivalTime([(1,2)], [0]) != 2, "spec negative 3";

  // From Neg 4: n=1, wrong=8
  expect ArrivalTime([(3,5)], [4]) != 8, "spec negative 4";

  // From Neg 5: n=2, wrong=13
  expect ArrivalTime([(2,4),(10,12)], [0,2]) != 13, "spec negative 5";

  // From Neg 6: n=3, wrong=10
  expect ArrivalTime([(1,3),(5,7),(9,11)], [0,0,0]) != 10, "spec negative 6";

  // From Neg 7: n=3, wrong=12
  expect ArrivalTime([(2,4),(6,8),(10,12)], [1,1,1]) != 12, "spec negative 7";

  // From Neg 8 case 1: n=1, wrong=2
  expect ArrivalTime([(1,2)], [0]) != 2, "spec negative 8";

  // From Neg 10 case 1: n=1, wrong=2
  expect ArrivalTime([(1,3)], [0]) != 2, "spec negative 10";

  // ═══════════════════════════════════════════════════
  // IMPLEMENTATION tests (full-size inputs)
  // ═══════════════════════════════════════════════════

  // Test 1 case 1: n=2
  var r1 := AlexeyAndTrain(2, [(2,4),(10,12)], [0,2]);
  expect r1 == 12, "impl test 1.1 failed";

  // Test 1 case 2: n=5
  var r2 := AlexeyAndTrain(5, [(1,4),(7,8),(9,10),(13,15),(19,20)], [1,2,3,4,5]);
  expect r2 == 32, "impl test 1.2 failed";

  // Test 2: n=1
  var r3 := AlexeyAndTrain(1, [(1,8)], [0]);
  expect r3 == 1, "impl test 2 failed";

  // Test 3: n=1
  var r4 := AlexeyAndTrain(1, [(1,2)], [0]);
  expect r4 == 1, "impl test 3 failed";

  // Test 4: n=1
  var r5 := AlexeyAndTrain(1, [(3,5)], [4]);
  expect r5 == 7, "impl test 4 failed";

  // Test 5: n=2
  var r6 := AlexeyAndTrain(2, [(2,4),(10,12)], [0,2]);
  expect r6 == 12, "impl test 5 failed";

  // Test 6: n=3
  var r7 := AlexeyAndTrain(3, [(1,3),(5,7),(9,11)], [0,0,0]);
  expect r7 == 9, "impl test 6 failed";

  // Test 7: n=3
  var r8 := AlexeyAndTrain(3, [(2,4),(6,8),(10,12)], [1,1,1]);
  expect r8 == 11, "impl test 7 failed";

  // Test 8 case 1: n=1
  var r9 := AlexeyAndTrain(1, [(1,2)], [0]);
  expect r9 == 1, "impl test 8.1 failed";

  // Test 8 case 2: n=1
  var r10 := AlexeyAndTrain(1, [(5,10)], [3]);
  expect r10 == 8, "impl test 8.2 failed";

  // Test 9: n=4
  var r11 := AlexeyAndTrain(4, [(1,2),(4,6),(8,10),(12,14)], [0,1,2,3]);
  expect r11 == 16, "impl test 9 failed";

  // Test 10 case 1: n=1
  var r12 := AlexeyAndTrain(1, [(1,3)], [0]);
  expect r12 == 1, "impl test 10.1 failed";

  // Test 10 case 2: n=2
  var r13 := AlexeyAndTrain(2, [(1,2),(5,8)], [1,0]);
  expect r13 == 6, "impl test 10.2 failed";

  // Test 10 case 3: n=1
  var r14 := AlexeyAndTrain(1, [(10,20)], [5]);
  expect r14 == 15, "impl test 10.3 failed";

  // Test 11: n=5
  var r15 := AlexeyAndTrain(5, [(1,3),(5,7),(9,11),(13,15),(17,19)], [2,2,2,2,2]);
  expect r15 == 23, "impl test 11 failed";

  // Test 12: n=10
  var r16 := AlexeyAndTrain(10, [(1,2),(4,5),(7,8),(10,11),(13,14),(16,17),(19,20),(22,23),(25,26),(28,30)], [0,0,0,0,0,0,0,0,0,0]);
  expect r16 == 28, "impl test 12 failed";

  print "All tests passed\n";
}
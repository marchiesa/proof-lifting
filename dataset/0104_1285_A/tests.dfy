function CountChar(s: string, c: char): int
  decreases |s|
{
  if |s| == 0 then 0
  else CountChar(s[..|s|-1], c) + (if s[|s|-1] == c then 1 else 0)
}

predicate Reachable(s: string, p: int)
{
  var l := CountChar(s, 'L');
  var r := CountChar(s, 'R');
  exists nl: int, nr: int | 0 <= nl <= l && 0 <= nr <= r :: p == nr - nl
}

function ReachablePositions(s: string): set<int>
{
  var l := CountChar(s, 'L');
  var r := CountChar(s, 'R');
  set p: int | -l <= p <= r && Reachable(s, p)
}

method MezoPlayingZoma(s: string) returns (positions: int)
  requires forall i | 0 <= i < |s| :: s[i] == 'L' || s[i] == 'R'
  ensures positions == |ReachablePositions(s)|
{
  var l := 0;
  var r := 0;
  for i := 0 to |s| {
    if s[i] == 'L' {
      l := l + 1;
    } else if s[i] == 'R' {
      r := r + 1;
    }
  }
  positions := l + r + 1;
}

method Main()
{
  // === SPEC POSITIVE TESTS ===
  // ensures: positions == |ReachablePositions(s)|
  // Using small inputs (length 1-3) to keep bounded quantifier evaluation fast

  // From test pair 2: "L" -> 2
  expect |ReachablePositions("L")| == 2, "spec positive 1";
  // From test pair 5: "R" -> 2
  expect |ReachablePositions("R")| == 2, "spec positive 2";
  // From test pair 4: "LR" -> 3
  expect |ReachablePositions("LR")| == 3, "spec positive 3";
  // Variant of test pair 4: "RL" -> 3
  expect |ReachablePositions("RL")| == 3, "spec positive 4";
  // Scaled from test pair 1 (LRLR, l=2,r=2): "LRL" (l=2,r=1) -> 4
  expect |ReachablePositions("LRL")| == 4, "spec positive 5";
  // Scaled from test pair 6 (all L's): "LL" (l=2,r=0) -> 3
  expect |ReachablePositions("LL")| == 3, "spec positive 6";

  // === SPEC NEGATIVE TESTS ===
  // Same predicate, wrong outputs — spec must reject these

  // From negative pair 2: "L" -> wrong 3
  expect |ReachablePositions("L")| != 3, "spec negative 1";
  // From negative pair 5: "R" -> wrong 3
  expect |ReachablePositions("R")| != 3, "spec negative 2";
  // From negative pair 4: "LR" -> wrong 4
  expect |ReachablePositions("LR")| != 4, "spec negative 3";
  // Variant: "RL" -> wrong 4
  expect |ReachablePositions("RL")| != 4, "spec negative 4";
  // Scaled from negative pair 1: "LRL" -> wrong 5
  expect |ReachablePositions("LRL")| != 5, "spec negative 5";
  // Scaled from negative pair 6: "LL" -> wrong 4
  expect |ReachablePositions("LL")| != 4, "spec negative 6";

  // === IMPLEMENTATION TESTS ===
  // Full-size inputs — the method is fast

  var r1 := MezoPlayingZoma("LRLR");
  expect r1 == 5, "impl test 1 failed";

  var r2 := MezoPlayingZoma("L");
  expect r2 == 2, "impl test 2 failed";

  var r3 := MezoPlayingZoma("LRLLLLRRLLRLR");
  expect r3 == 14, "impl test 3 failed";

  var r4 := MezoPlayingZoma("LR");
  expect r4 == 3, "impl test 4 failed";

  var r5 := MezoPlayingZoma("R");
  expect r5 == 2, "impl test 5 failed";

  var r6 := MezoPlayingZoma("LLLLLLLLLLLL");
  expect r6 == 13, "impl test 6 failed";

  print "All tests passed\n";
}
function GCD(a: int, b: int): int
  requires a > 0 && b >= 0
  ensures GCD(a, b) > 0
  decreases b
{
  if b == 0 then a else GCD(b, a % b)
}

function LCM(a: int, b: int): int
  requires a > 0 && b > 0
{
  (a / GCD(a, b)) * b
}

predicate ValidPair(x: int, y: int, l: int, r: int)
  requires l >= 1
{
  l <= x && x < y && y <= r && l <= LCM(x, y) && LCM(x, y) <= r
}

predicate PairExists(l: int, r: int)
  requires l >= 1
{
  exists x | l <= x <= r :: exists y | x + 1 <= y <= r :: ValidPair(x, y, l, r)
}

method LCMProblem(l: int, r: int) returns (x: int, y: int)
  requires l >= 1
  ensures (x == -1 && y == -1) || ValidPair(x, y, l, r)
  ensures (x == -1 && y == -1) <==> !PairExists(l, r)
{
  if l * 2 > r {
    return -1, -1;
  } else {
    return l, l * 2;
  }
}

predicate Spec(l: int, r: int, x: int, y: int)
  requires l >= 1
{
  ((x == -1 && y == -1) || ValidPair(x, y, l, r)) &&
  ((x == -1 && y == -1) <==> !PairExists(l, r))
}

method Main()
{
  // === SPEC POSITIVE TESTS ===
  // Small inputs so PairExists bounded quantifiers are feasible
  // SP1: (l=1,r=2) -> (1,2), scaled from Test 9
  expect Spec(1, 2, 1, 2), "spec positive 1";
  // SP2: (l=2,r=4) -> (2,4), from Test 3
  expect Spec(2, 4, 2, 4), "spec positive 2";
  // SP3: (l=1,r=3) -> (1,2), scaled from Test 1
  expect Spec(1, 3, 1, 2), "spec positive 3";
  // SP4: (l=3,r=6) -> (3,6), scaled from Test 4/8
  expect Spec(3, 6, 3, 6), "spec positive 4";
  // SP5: (l=2,r=3) -> (-1,-1), scaled from Test 2 (no valid pair)
  expect Spec(2, 3, -1, -1), "spec positive 5";
  // SP6: (l=3,r=5) -> (-1,-1), scaled from Test 4 (no valid pair)
  expect Spec(3, 5, -1, -1), "spec positive 6";
  // SP7: (l=1,r=4) -> (1,2), scaled from Test 7
  expect Spec(1, 4, 1, 2), "spec positive 7";

  // === SPEC NEGATIVE TESTS ===
  // Wrong outputs must be rejected by the spec
  // SN1: wrong (2,2) — x < y violated, scaled from Neg 1
  expect !Spec(1, 2, 2, 2), "spec negative 1";
  // SN2: wrong (0,-1) — not (-1,-1) and not valid, scaled from Neg 2
  expect !Spec(2, 3, 0, -1), "spec negative 2";
  // SN3: wrong (3,4) — LCM(3,4)=12 > r=4, from Neg 3
  expect !Spec(2, 4, 3, 4), "spec negative 3";
  // SN4: wrong (2,3) — LCM(2,3)=6 > r=3, scaled from Neg 4
  expect !Spec(1, 3, 2, 3), "spec negative 4";
  // SN5: wrong (4,6) — LCM(4,6)=12 > r=6, scaled from Neg 5
  expect !Spec(3, 6, 4, 6), "spec negative 5";
  // SN6: wrong (2,3) — LCM(2,3)=6 > r=4, scaled from Neg 6
  expect !Spec(1, 4, 2, 3), "spec negative 6";
  // SN7: wrong (2,1) — x < y violated, scaled from Neg 7
  expect !Spec(1, 2, 2, 1), "spec negative 7";
  // SN8: wrong (4,5) — LCM(4,5)=20 > r=6, scaled from Neg 8
  expect !Spec(3, 6, 4, 5), "spec negative 8";
  // SN9: wrong (2,2) — x < y violated, scaled from Neg 9
  expect !Spec(1, 3, 2, 2), "spec negative 9";

  // === IMPLEMENTATION TESTS ===
  // Test 1
  var x1, y1 := LCMProblem(1, 1337);
  expect x1 == 1 && y1 == 2, "impl test 1 failed";

  var x2, y2 := LCMProblem(13, 69);
  expect x2 == 13 && y2 == 26, "impl test 2 failed";

  var x3, y3 := LCMProblem(2, 4);
  expect x3 == 2 && y3 == 4, "impl test 3 failed";

  var x4, y4 := LCMProblem(88, 89);
  expect x4 == -1 && y4 == -1, "impl test 4 failed";

  // Test 2
  var x5, y5 := LCMProblem(55556, 55557);
  expect x5 == -1 && y5 == -1, "impl test 5 failed";

  // Test 3 (5 repeated cases)
  var i := 0;
  while i < 5 {
    var a, b := LCMProblem(2, 4);
    expect a == 2 && b == 4, "impl test 6 failed";
    i := i + 1;
  }

  // Test 4
  var x6, y6 := LCMProblem(78788, 157576);
  expect x6 == 78788 && y6 == 157576, "impl test 7 failed";

  // Test 5
  var x7, y7 := LCMProblem(8743, 17489);
  expect x7 == 8743 && y7 == 17486, "impl test 8 failed";

  // Test 6
  var x8, y8 := LCMProblem(96777, 19555557);
  expect x8 == 96777 && y8 == 193554, "impl test 9 failed";

  // Test 7
  var x9, y9 := LCMProblem(1000003, 100000000);
  expect x9 == 1000003 && y9 == 2000006, "impl test 10 failed";

  // Test 8
  var x10, y10 := LCMProblem(80000000, 160000000);
  expect x10 == 80000000 && y10 == 160000000, "impl test 11 failed";

  // Test 9 (69 repeated cases)
  var j := 0;
  while j < 69 {
    var a, b := LCMProblem(1, 2);
    expect a == 1 && b == 2, "impl test 12 failed";
    j := j + 1;
  }

  print "All tests passed\n";
}
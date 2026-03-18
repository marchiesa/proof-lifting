// ─────────────── Arithmetic helpers ───────────────

function Abs(x: int): int {
  if x >= 0 then x else -x
}

function Max(x: int, y: int): int {
  if x >= y then x else y
}

function Min(x: int, y: int): int {
  if x <= y then x else y
}

// ─────────────── Sorting three values ───────────────

function Min3(a: int, b: int, c: int): int {
  Min(a, Min(b, c))
}

function Max3(a: int, b: int, c: int): int {
  Max(a, Max(b, c))
}

function Mid3(a: int, b: int, c: int): int {
  a + b + c - Min3(a, b, c) - Max3(a, b, c)
}

// ─────────────── Problem-level predicates ───────────────

predicate AllPairsSeparated(p: int, q: int, r: int, d: int) {
  Abs(p - q) >= d && Abs(p - r) >= d && Abs(q - r) >= d
}

function TotalMoves(a: int, b: int, c: int, a': int, b': int, c': int): int {
  Abs(a - a') + Abs(b - b') + Abs(c - c')
}

// ─────────────── Witness: optimal final positions ───────────────

function OptimalLo(a: int, b: int, c: int, d: int): int {
  Min(Min3(a, b, c), Mid3(a, b, c) - d)
}

function OptimalMid(a: int, b: int, c: int, d: int): int {
  Mid3(a, b, c)
}

function OptimalHi(a: int, b: int, c: int, d: int): int {
  Max(Max3(a, b, c), Mid3(a, b, c) + d)
}

// ─────────────── Minimum moves ───────────────

function MinimumMoves(a: int, b: int, c: int, d: int): int {
  Max(0, d - (Mid3(a, b, c) - Min3(a, b, c)))
  + Max(0, d - (Max3(a, b, c) - Mid3(a, b, c)))
}

// ═══════════════════════════════════════════════════════

method Ropewalkers(a: int, b: int, c: int, d: int) returns (result: int)
  ensures result == MinimumMoves(a, b, c, d)
  ensures result >= 0
  ensures AllPairsSeparated(OptimalLo(a, b, c, d), OptimalMid(a, b, c, d), OptimalHi(a, b, c, d), d)
  ensures TotalMoves(Min3(a, b, c), Mid3(a, b, c), Max3(a, b, c),
                     OptimalLo(a, b, c, d), OptimalMid(a, b, c, d), OptimalHi(a, b, c, d)) == result
{
  var x := a;
  var y := b;
  var z := c;

  if x > y {
    var tmp := x;
    x := y;
    y := tmp;
  }
  if y > z {
    var tmp := y;
    y := z;
    z := tmp;
  }
  if x > y {
    var tmp := x;
    x := y;
    y := tmp;
  }

  var val1 := d - (y - x);
  var val2 := d - (z - y);
  if val1 < 0 { val1 := 0; }
  if val2 < 0 { val2 := 0; }

  result := val1 + val2;
}

method Main()
{
  // ════════════════════════════════════════════
  // (a) SPEC POSITIVE tests — ensures predicates hold for correct outputs
  // ════════════════════════════════════════════

  // Test ensures #1: result == MinimumMoves(a, b, c, d)
  expect MinimumMoves(5, 2, 6, 3) == 2, "spec positive 1";
  expect MinimumMoves(3, 1, 5, 6) == 8, "spec positive 2";
  expect MinimumMoves(8, 3, 3, 2) == 2, "spec positive 3";
  expect MinimumMoves(2, 3, 10, 4) == 3, "spec positive 4";
  expect MinimumMoves(1000000000, 1000000000, 1000000000, 1000000000) == 2000000000, "spec positive 5";
  expect MinimumMoves(500000000, 250000000, 750000000, 1000000000) == 1500000000, "spec positive 6";
  expect MinimumMoves(1, 3, 2, 5) == 8, "spec positive 7";
  expect MinimumMoves(2, 3, 1, 6) == 10, "spec positive 8";
  expect MinimumMoves(9, 6, 2, 5) == 3, "spec positive 9";
  expect MinimumMoves(1, 1, 1, 1) == 2, "spec positive 10";

  // Test ensures #2: result >= 0
  expect 2 >= 0, "spec positive non-neg 1";
  expect 8 >= 0, "spec positive non-neg 2";
  expect 2 >= 0, "spec positive non-neg 3";
  expect 3 >= 0, "spec positive non-neg 4";
  expect 2000000000 >= 0, "spec positive non-neg 5";
  expect 1500000000 >= 0, "spec positive non-neg 6";
  expect 8 >= 0, "spec positive non-neg 7";
  expect 10 >= 0, "spec positive non-neg 8";
  expect 3 >= 0, "spec positive non-neg 9";
  expect 2 >= 0, "spec positive non-neg 10";

  // Test ensures #3: AllPairsSeparated(OptimalLo, OptimalMid, OptimalHi, d)
  expect AllPairsSeparated(OptimalLo(5,2,6,3), OptimalMid(5,2,6,3), OptimalHi(5,2,6,3), 3), "spec positive sep 1";
  expect AllPairsSeparated(OptimalLo(3,1,5,6), OptimalMid(3,1,5,6), OptimalHi(3,1,5,6), 6), "spec positive sep 2";
  expect AllPairsSeparated(OptimalLo(8,3,3,2), OptimalMid(8,3,3,2), OptimalHi(8,3,3,2), 2), "spec positive sep 3";
  expect AllPairsSeparated(OptimalLo(2,3,10,4), OptimalMid(2,3,10,4), OptimalHi(2,3,10,4), 4), "spec positive sep 4";
  expect AllPairsSeparated(OptimalLo(1000000000,1000000000,1000000000,1000000000), OptimalMid(1000000000,1000000000,1000000000,1000000000), OptimalHi(1000000000,1000000000,1000000000,1000000000), 1000000000), "spec positive sep 5";
  expect AllPairsSeparated(OptimalLo(500000000,250000000,750000000,1000000000), OptimalMid(500000000,250000000,750000000,1000000000), OptimalHi(500000000,250000000,750000000,1000000000), 1000000000), "spec positive sep 6";
  expect AllPairsSeparated(OptimalLo(1,3,2,5), OptimalMid(1,3,2,5), OptimalHi(1,3,2,5), 5), "spec positive sep 7";
  expect AllPairsSeparated(OptimalLo(2,3,1,6), OptimalMid(2,3,1,6), OptimalHi(2,3,1,6), 6), "spec positive sep 8";
  expect AllPairsSeparated(OptimalLo(9,6,2,5), OptimalMid(9,6,2,5), OptimalHi(9,6,2,5), 5), "spec positive sep 9";
  expect AllPairsSeparated(OptimalLo(1,1,1,1), OptimalMid(1,1,1,1), OptimalHi(1,1,1,1), 1), "spec positive sep 10";

  // Test ensures #4: TotalMoves(sorted_orig, optimal) == result
  expect TotalMoves(Min3(5,2,6), Mid3(5,2,6), Max3(5,2,6), OptimalLo(5,2,6,3), OptimalMid(5,2,6,3), OptimalHi(5,2,6,3)) == 2, "spec positive cost 1";
  expect TotalMoves(Min3(3,1,5), Mid3(3,1,5), Max3(3,1,5), OptimalLo(3,1,5,6), OptimalMid(3,1,5,6), OptimalHi(3,1,5,6)) == 8, "spec positive cost 2";
  expect TotalMoves(Min3(8,3,3), Mid3(8,3,3), Max3(8,3,3), OptimalLo(8,3,3,2), OptimalMid(8,3,3,2), OptimalHi(8,3,3,2)) == 2, "spec positive cost 3";
  expect TotalMoves(Min3(2,3,10), Mid3(2,3,10), Max3(2,3,10), OptimalLo(2,3,10,4), OptimalMid(2,3,10,4), OptimalHi(2,3,10,4)) == 3, "spec positive cost 4";
  expect TotalMoves(Min3(1000000000,1000000000,1000000000), Mid3(1000000000,1000000000,1000000000), Max3(1000000000,1000000000,1000000000), OptimalLo(1000000000,1000000000,1000000000,1000000000), OptimalMid(1000000000,1000000000,1000000000,1000000000), OptimalHi(1000000000,1000000000,1000000000,1000000000)) == 2000000000, "spec positive cost 5";
  expect TotalMoves(Min3(500000000,250000000,750000000), Mid3(500000000,250000000,750000000), Max3(500000000,250000000,750000000), OptimalLo(500000000,250000000,750000000,1000000000), OptimalMid(500000000,250000000,750000000,1000000000), OptimalHi(500000000,250000000,750000000,1000000000)) == 1500000000, "spec positive cost 6";
  expect TotalMoves(Min3(1,3,2), Mid3(1,3,2), Max3(1,3,2), OptimalLo(1,3,2,5), OptimalMid(1,3,2,5), OptimalHi(1,3,2,5)) == 8, "spec positive cost 7";
  expect TotalMoves(Min3(2,3,1), Mid3(2,3,1), Max3(2,3,1), OptimalLo(2,3,1,6), OptimalMid(2,3,1,6), OptimalHi(2,3,1,6)) == 10, "spec positive cost 8";
  expect TotalMoves(Min3(9,6,2), Mid3(9,6,2), Max3(9,6,2), OptimalLo(9,6,2,5), OptimalMid(9,6,2,5), OptimalHi(9,6,2,5)) == 3, "spec positive cost 9";
  expect TotalMoves(Min3(1,1,1), Mid3(1,1,1), Max3(1,1,1), OptimalLo(1,1,1,1), OptimalMid(1,1,1,1), OptimalHi(1,1,1,1)) == 2, "spec positive cost 10";

  // ════════════════════════════════════════════
  // (b) SPEC NEGATIVE tests — ensures predicates reject wrong outputs
  // ════════════════════════════════════════════

  expect !(MinimumMoves(5, 2, 6, 3) == 3), "spec negative 1";
  expect !(MinimumMoves(3, 1, 5, 6) == 9), "spec negative 2";
  expect !(MinimumMoves(8, 3, 3, 2) == 3), "spec negative 3";
  expect !(MinimumMoves(2, 3, 10, 4) == 4), "spec negative 4";
  expect !(MinimumMoves(1000000000, 1000000000, 1000000000, 1000000000) == 2000000001), "spec negative 5";
  expect !(MinimumMoves(500000000, 250000000, 750000000, 1000000000) == 1500000001), "spec negative 6";
  expect !(MinimumMoves(1, 3, 2, 5) == 9), "spec negative 7";
  expect !(MinimumMoves(2, 3, 1, 6) == 11), "spec negative 8";
  expect !(MinimumMoves(9, 6, 2, 5) == 4), "spec negative 9";
  expect !(MinimumMoves(1, 1, 1, 1) == 3), "spec negative 10";

  // ════════════════════════════════════════════
  // (c) IMPLEMENTATION tests — call method, check result
  // ════════════════════════════════════════════

  var r: int;

  r := Ropewalkers(5, 2, 6, 3);
  expect r == 2, "impl test 1 failed";

  r := Ropewalkers(3, 1, 5, 6);
  expect r == 8, "impl test 2 failed";

  r := Ropewalkers(8, 3, 3, 2);
  expect r == 2, "impl test 3 failed";

  r := Ropewalkers(2, 3, 10, 4);
  expect r == 3, "impl test 4 failed";

  r := Ropewalkers(1000000000, 1000000000, 1000000000, 1000000000);
  expect r == 2000000000, "impl test 5 failed";

  r := Ropewalkers(500000000, 250000000, 750000000, 1000000000);
  expect r == 1500000000, "impl test 6 failed";

  r := Ropewalkers(1, 3, 2, 5);
  expect r == 8, "impl test 7 failed";

  r := Ropewalkers(2, 3, 1, 6);
  expect r == 10, "impl test 8 failed";

  r := Ropewalkers(9, 6, 2, 5);
  expect r == 3, "impl test 9 failed";

  r := Ropewalkers(1, 1, 1, 1);
  expect r == 2, "impl test 10 failed";

  r := Ropewalkers(1, 1, 500, 10);
  expect r == 10, "impl test 11 failed";

  r := Ropewalkers(500, 1, 500, 1000);
  expect r == 1501, "impl test 12 failed";

  r := Ropewalkers(1, 2, 1, 1);
  expect r == 1, "impl test 13 failed";

  r := Ropewalkers(89, 983, 751, 1000);
  expect r == 1106, "impl test 14 failed";

  r := Ropewalkers(716270982, 22102638, 553198855, 1000000000);
  expect r == 1305831656, "impl test 15 failed";

  r := Ropewalkers(1000000000, 1, 1000000000, 999999999);
  expect r == 999999999, "impl test 16 failed";

  r := Ropewalkers(999999999, 1, 1, 1000000000);
  expect r == 1000000002, "impl test 17 failed";

  r := Ropewalkers(1, 2, 3, 4);
  expect r == 6, "impl test 18 failed";

  r := Ropewalkers(1, 3, 4, 5);
  expect r == 7, "impl test 19 failed";

  r := Ropewalkers(1, 3, 2, 6);
  expect r == 10, "impl test 20 failed";

  print "All tests passed\n";
}
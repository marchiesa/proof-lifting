predicate Feasible(a: int, b: int, c: int, x: int, y: int) {
  x >= 0 && y >= 0 && x <= a && 2 * x + y <= b && 2 * y <= c
}

function StonesCollected(x: int, y: int): int {
  3 * (x + y)
}

// Top-level spec predicate: combines both ensures clauses
predicate StonesSpec(a: int, b: int, c: int, maxStones: int)
  requires a >= 0 && b >= 0 && c >= 0
{
  (exists x: int | 0 <= x <= a ::
    exists y: int | 0 <= y <= c / 2 ::
      Feasible(a, b, c, x, y) && maxStones == StonesCollected(x, y))
  &&
  (forall x: int | 0 <= x <= a ::
    forall y: int | 0 <= y <= c / 2 ::
      Feasible(a, b, c, x, y) ==> StonesCollected(x, y) <= maxStones)
}

method Stones(a: int, b: int, c: int) returns (maxStones: int)
  requires a >= 0 && b >= 0 && c >= 0
  ensures exists x: int | 0 <= x <= a ::
            exists y: int | 0 <= y <= c / 2 ::
              Feasible(a, b, c, x, y) && maxStones == StonesCollected(x, y)
  ensures forall x: int | 0 <= x <= a ::
            forall y: int | 0 <= y <= c / 2 ::
              Feasible(a, b, c, x, y) ==> StonesCollected(x, y) <= maxStones
{
  var c2 := if c / 2 < b then c / 2 else b;
  var rem := if (b - c2) / 2 < a then (b - c2) / 2 else a;
  maxStones := (c2 + rem) * 3;
}

method Main()
{
  var r: int;

  // ===== SPEC POSITIVE TESTS (small inputs, values 0-5) =====

  // From Test 1 (all values <= 5)
  expect StonesSpec(3, 4, 5, 9), "spec positive 1a";
  expect StonesSpec(1, 0, 5, 0), "spec positive 1b";
  expect StonesSpec(5, 3, 2, 6), "spec positive 1c";

  // From Test 2 (exhaustive 0..3)
  expect StonesSpec(0, 0, 0, 0), "spec positive 2a";
  expect StonesSpec(0, 0, 1, 0), "spec positive 2b";
  expect StonesSpec(0, 0, 2, 0), "spec positive 2c";
  expect StonesSpec(0, 0, 3, 0), "spec positive 2d";
  expect StonesSpec(0, 1, 0, 0), "spec positive 2e";
  expect StonesSpec(0, 1, 1, 0), "spec positive 2f";
  expect StonesSpec(0, 1, 2, 3), "spec positive 2g";
  expect StonesSpec(0, 1, 3, 3), "spec positive 2h";
  expect StonesSpec(0, 2, 0, 0), "spec positive 2i";
  expect StonesSpec(0, 2, 1, 0), "spec positive 2j";
  expect StonesSpec(0, 2, 2, 3), "spec positive 2k";
  expect StonesSpec(0, 2, 3, 3), "spec positive 2l";
  expect StonesSpec(0, 3, 0, 0), "spec positive 2m";
  expect StonesSpec(0, 3, 1, 0), "spec positive 2n";
  expect StonesSpec(0, 3, 2, 3), "spec positive 2o";
  expect StonesSpec(0, 3, 3, 3), "spec positive 2p";
  expect StonesSpec(1, 0, 0, 0), "spec positive 2q";
  expect StonesSpec(1, 0, 1, 0), "spec positive 2r";
  expect StonesSpec(1, 0, 2, 0), "spec positive 2s";
  expect StonesSpec(1, 0, 3, 0), "spec positive 2t";
  expect StonesSpec(1, 1, 0, 0), "spec positive 2u";
  expect StonesSpec(1, 1, 1, 0), "spec positive 2v";
  expect StonesSpec(1, 1, 2, 3), "spec positive 2w";
  expect StonesSpec(1, 1, 3, 3), "spec positive 2x";
  expect StonesSpec(1, 2, 0, 3), "spec positive 2y";
  expect StonesSpec(1, 2, 1, 3), "spec positive 2z";
  expect StonesSpec(1, 2, 2, 3), "spec positive 2aa";
  expect StonesSpec(1, 2, 3, 3), "spec positive 2ab";
  expect StonesSpec(1, 3, 0, 3), "spec positive 2ac";
  expect StonesSpec(1, 3, 1, 3), "spec positive 2ad";
  expect StonesSpec(1, 3, 2, 6), "spec positive 2ae";
  expect StonesSpec(1, 3, 3, 6), "spec positive 2af";
  expect StonesSpec(2, 0, 0, 0), "spec positive 2ag";
  expect StonesSpec(2, 0, 1, 0), "spec positive 2ah";
  expect StonesSpec(2, 0, 2, 0), "spec positive 2ai";
  expect StonesSpec(2, 0, 3, 0), "spec positive 2aj";
  expect StonesSpec(2, 1, 0, 0), "spec positive 2ak";
  expect StonesSpec(2, 1, 1, 0), "spec positive 2al";
  expect StonesSpec(2, 1, 2, 3), "spec positive 2am";
  expect StonesSpec(2, 1, 3, 3), "spec positive 2an";
  expect StonesSpec(2, 2, 0, 3), "spec positive 2ao";
  expect StonesSpec(2, 2, 1, 3), "spec positive 2ap";
  expect StonesSpec(2, 2, 2, 3), "spec positive 2aq";
  expect StonesSpec(2, 2, 3, 3), "spec positive 2ar";
  expect StonesSpec(2, 3, 0, 3), "spec positive 2as";
  expect StonesSpec(2, 3, 1, 3), "spec positive 2at";
  expect StonesSpec(2, 3, 2, 6), "spec positive 2au";
  expect StonesSpec(2, 3, 3, 6), "spec positive 2av";
  expect StonesSpec(3, 0, 0, 0), "spec positive 2aw";
  expect StonesSpec(3, 0, 1, 0), "spec positive 2ax";
  expect StonesSpec(3, 0, 2, 0), "spec positive 2ay";
  expect StonesSpec(3, 0, 3, 0), "spec positive 2az";
  expect StonesSpec(3, 1, 0, 0), "spec positive 2ba";
  expect StonesSpec(3, 1, 1, 0), "spec positive 2bb";
  expect StonesSpec(3, 1, 2, 3), "spec positive 2bc";
  expect StonesSpec(3, 1, 3, 3), "spec positive 2bd";
  expect StonesSpec(3, 2, 0, 3), "spec positive 2be";
  expect StonesSpec(3, 2, 1, 3), "spec positive 2bf";
  expect StonesSpec(3, 2, 2, 3), "spec positive 2bg";
  expect StonesSpec(3, 2, 3, 3), "spec positive 2bh";
  expect StonesSpec(3, 3, 0, 3), "spec positive 2bi";
  expect StonesSpec(3, 3, 1, 3), "spec positive 2bj";
  expect StonesSpec(3, 3, 2, 6), "spec positive 2bk";
  expect StonesSpec(3, 3, 3, 6), "spec positive 2bl";

  // From Test 3 (only small case)
  expect StonesSpec(0, 0, 0, 0), "spec positive 3a";

  // From Test 4 (small cases with all values <= 5)
  expect StonesSpec(4, 2, 1, 3), "spec positive 4a";
  expect StonesSpec(4, 4, 0, 6), "spec positive 4b";
  expect StonesSpec(2, 0, 0, 0), "spec positive 4c";
  expect StonesSpec(4, 0, 0, 0), "spec positive 4d";

  // From Test 5 (small cases)
  expect StonesSpec(0, 0, 1, 0), "spec positive 5a";
  expect StonesSpec(2, 3, 0, 3), "spec positive 5b";
  expect StonesSpec(1, 3, 4, 6), "spec positive 5c";
  expect StonesSpec(4, 1, 2, 3), "spec positive 5d";

  // From Test 6 (small case)
  expect StonesSpec(1, 4, 2, 6), "spec positive 6a";

  // From Test 7 (no cases with all values <= 5; skip)

  // From Test 8 (small cases)
  expect StonesSpec(3, 2, 4, 6), "spec positive 8a";
  expect StonesSpec(4, 2, 1, 3), "spec positive 8b";
  expect StonesSpec(3, 3, 2, 6), "spec positive 8c";
  expect StonesSpec(0, 0, 0, 0), "spec positive 8d";

  // ===== SPEC NEGATIVE TESTS (wrong outputs the spec must reject) =====

  // Neg 1: (3,4,5) wrong=10, correct=9
  expect !StonesSpec(3, 4, 5, 10), "spec negative 1";
  // Neg 2: (0,0,0) wrong=1, correct=0
  expect !StonesSpec(0, 0, 0, 1), "spec negative 2";
  // Neg 3: scaled from (100,100,100)->226 to (5,5,5)->10, correct=9
  expect !StonesSpec(5, 5, 5, 10), "spec negative 3";
  // Neg 4: scaled from (9,4,8)->13 to (3,2,4)->7, correct=6
  expect !StonesSpec(3, 2, 4, 7), "spec negative 4";
  // Neg 5: scaled from (4,4,8)->13 to (4,4,4)->10, correct=9
  expect !StonesSpec(4, 4, 4, 10), "spec negative 5";
  // Neg 6: scaled from (0,2,9)->7 to (0,2,4)->7, correct=6
  expect !StonesSpec(0, 2, 4, 7), "spec negative 6";
  // Neg 7: scaled from (6,0,8)->1 to (3,0,4)->1, correct=0
  expect !StonesSpec(3, 0, 4, 1), "spec negative 7";
  // Neg 8: scaled from (2,0,8)->1 to (2,0,4)->1, correct=0
  expect !StonesSpec(2, 0, 4, 1), "spec negative 8";

  // ===== IMPLEMENTATION TESTS =====

  // Test 1
  r := Stones(3, 4, 5); expect r == 9, "impl 1a";
  r := Stones(1, 0, 5); expect r == 0, "impl 1b";
  r := Stones(5, 3, 2); expect r == 6, "impl 1c";

  // Test 2 (exhaustive 0..3)
  r := Stones(0, 0, 0); expect r == 0, "impl 2a";
  r := Stones(0, 0, 1); expect r == 0, "impl 2b";
  r := Stones(0, 0, 2); expect r == 0, "impl 2c";
  r := Stones(0, 0, 3); expect r == 0, "impl 2d";
  r := Stones(0, 1, 0); expect r == 0, "impl 2e";
  r := Stones(0, 1, 1); expect r == 0, "impl 2f";
  r := Stones(0, 1, 2); expect r == 3, "impl 2g";
  r := Stones(0, 1, 3); expect r == 3, "impl 2h";
  r := Stones(0, 2, 0); expect r == 0, "impl 2i";
  r := Stones(0, 2, 1); expect r == 0, "impl 2j";
  r := Stones(0, 2, 2); expect r == 3, "impl 2k";
  r := Stones(0, 2, 3); expect r == 3, "impl 2l";
  r := Stones(0, 3, 0); expect r == 0, "impl 2m";
  r := Stones(0, 3, 1); expect r == 0, "impl 2n";
  r := Stones(0, 3, 2); expect r == 3, "impl 2o";
  r := Stones(0, 3, 3); expect r == 3, "impl 2p";
  r := Stones(1, 0, 0); expect r == 0, "impl 2q";
  r := Stones(1, 0, 1); expect r == 0, "impl 2r";
  r := Stones(1, 0, 2); expect r == 0, "impl 2s";
  r := Stones(1, 0, 3); expect r == 0, "impl 2t";
  r := Stones(1, 1, 0); expect r == 0, "impl 2u";
  r := Stones(1, 1, 1); expect r == 0, "impl 2v";
  r := Stones(1, 1, 2); expect r == 3, "impl 2w";
  r := Stones(1, 1, 3); expect r == 3, "impl 2x";
  r := Stones(1, 2, 0); expect r == 3, "impl 2y";
  r := Stones(1, 2, 1); expect r == 3, "impl 2z";
  r := Stones(1, 2, 2); expect r == 3, "impl 2aa";
  r := Stones(1, 2, 3); expect r == 3, "impl 2ab";
  r := Stones(1, 3, 0); expect r == 3, "impl 2ac";
  r := Stones(1, 3, 1); expect r == 3, "impl 2ad";
  r := Stones(1, 3, 2); expect r == 6, "impl 2ae";
  r := Stones(1, 3, 3); expect r == 6, "impl 2af";
  r := Stones(2, 0, 0); expect r == 0, "impl 2ag";
  r := Stones(2, 0, 1); expect r == 0, "impl 2ah";
  r := Stones(2, 0, 2); expect r == 0, "impl 2ai";
  r := Stones(2, 0, 3); expect r == 0, "impl 2aj";
  r := Stones(2, 1, 0); expect r == 0, "impl 2ak";
  r := Stones(2, 1, 1); expect r == 0, "impl 2al";
  r := Stones(2, 1, 2); expect r == 3, "impl 2am";
  r := Stones(2, 1, 3); expect r == 3, "impl 2an";
  r := Stones(2, 2, 0); expect r == 3, "impl 2ao";
  r := Stones(2, 2, 1); expect r == 3, "impl 2ap";
  r := Stones(2, 2, 2); expect r == 3, "impl 2aq";
  r := Stones(2, 2, 3); expect r == 3, "impl 2ar";
  r := Stones(2, 3, 0); expect r == 3, "impl 2as";
  r := Stones(2, 3, 1); expect r == 3, "impl 2at";
  r := Stones(2, 3, 2); expect r == 6, "impl 2au";
  r := Stones(2, 3, 3); expect r == 6, "impl 2av";
  r := Stones(3, 0, 0); expect r == 0, "impl 2aw";
  r := Stones(3, 0, 1); expect r == 0, "impl 2ax";
  r := Stones(3, 0, 2); expect r == 0, "impl 2ay";
  r := Stones(3, 0, 3); expect r == 0, "impl 2az";
  r := Stones(3, 1, 0); expect r == 0, "impl 2ba";
  r := Stones(3, 1, 1); expect r == 0, "impl 2bb";
  r := Stones(3, 1, 2); expect r == 3, "impl 2bc";
  r := Stones(3, 1, 3); expect r == 3, "impl 2bd";
  r := Stones(3, 2, 0); expect r == 3, "impl 2be";
  r := Stones(3, 2, 1); expect r == 3, "impl 2bf";
  r := Stones(3, 2, 2); expect r == 3, "impl 2bg";
  r := Stones(3, 2, 3); expect r == 3, "impl 2bh";
  r := Stones(3, 3, 0); expect r == 3, "impl 2bi";
  r := Stones(3, 3, 1); expect r == 3, "impl 2bj";
  r := Stones(3, 3, 2); expect r == 6, "impl 2bk";
  r := Stones(3, 3, 3); expect r == 6, "impl 2bl";

  // Test 3
  r := Stones(100, 100, 100); expect r == 225, "impl 3a";
  r := Stones(0, 0, 0); expect r == 0, "impl 3b";
  r := Stones(0, 50, 100); expect r == 150, "impl 3c";
  r := Stones(100, 50, 0); expect r == 75, "impl 3d";
  r := Stones(100, 30, 100); expect r == 90, "impl 3e";

  // Test 4
  r := Stones(9, 4, 8); expect r == 12, "impl 4a";
  r := Stones(10, 6, 7); expect r == 12, "impl 4b";
  r := Stones(4, 6, 0); expect r == 9, "impl 4c";
  r := Stones(7, 7, 6); expect r == 15, "impl 4d";
  r := Stones(3, 3, 10); expect r == 9, "impl 4e";
  r := Stones(4, 2, 1); expect r == 3, "impl 4f";
  r := Stones(4, 4, 0); expect r == 6, "impl 4g";
  r := Stones(2, 0, 0); expect r == 0, "impl 4h";
  r := Stones(8, 8, 7); expect r == 15, "impl 4i";
  r := Stones(3, 1, 7); expect r == 3, "impl 4j";
  r := Stones(3, 10, 7); expect r == 18, "impl 4k";
  r := Stones(1, 7, 3); expect r == 6, "impl 4l";
  r := Stones(7, 9, 1); expect r == 12, "impl 4m";
  r := Stones(1, 6, 9); expect r == 15, "impl 4n";
  r := Stones(0, 9, 5); expect r == 6, "impl 4o";
  r := Stones(4, 0, 0); expect r == 0, "impl 4p";
  r := Stones(2, 10, 0); expect r == 6, "impl 4q";
  r := Stones(4, 8, 5); expect r == 15, "impl 4r";
  r := Stones(10, 0, 1); expect r == 0, "impl 4s";
  r := Stones(8, 1, 1); expect r == 0, "impl 4t";

  // Test 5
  r := Stones(4, 4, 8); expect r == 12, "impl 5a";
  r := Stones(5, 3, 7); expect r == 9, "impl 5b";
  r := Stones(0, 0, 1); expect r == 0, "impl 5c";
  r := Stones(2, 3, 8); expect r == 9, "impl 5d";
  r := Stones(9, 4, 10); expect r == 12, "impl 5e";
  r := Stones(4, 8, 10); expect r == 18, "impl 5f";
  r := Stones(6, 3, 4); expect r == 6, "impl 5g";
  r := Stones(10, 10, 0); expect r == 15, "impl 5h";
  r := Stones(0, 7, 4); expect r == 6, "impl 5i";
  r := Stones(6, 2, 2); expect r == 3, "impl 5j";
  r := Stones(3, 10, 2); expect r == 12, "impl 5k";
  r := Stones(2, 7, 6); expect r == 15, "impl 5l";
  r := Stones(1, 2, 6); expect r == 6, "impl 5m";
  r := Stones(2, 3, 0); expect r == 3, "impl 5n";
  r := Stones(1, 3, 4); expect r == 6, "impl 5o";
  r := Stones(5, 0, 10); expect r == 0, "impl 5p";
  r := Stones(4, 1, 2); expect r == 3, "impl 5q";
  r := Stones(3, 7, 7); expect r == 15, "impl 5r";
  r := Stones(7, 10, 5); expect r == 18, "impl 5s";
  r := Stones(0, 9, 0); expect r == 0, "impl 5t";

  // Test 6
  r := Stones(0, 2, 9); expect r == 6, "impl 6a";
  r := Stones(2, 9, 7); expect r == 15, "impl 6b";
  r := Stones(7, 3, 3); expect r == 6, "impl 6c";
  r := Stones(9, 0, 10); expect r == 0, "impl 6d";
  r := Stones(4, 8, 0); expect r == 12, "impl 6e";
  r := Stones(2, 3, 9); expect r == 9, "impl 6f";
  r := Stones(7, 0, 8); expect r == 0, "impl 6g";
  r := Stones(5, 8, 10); expect r == 18, "impl 6h";
  r := Stones(1, 4, 2); expect r == 6, "impl 6i";
  r := Stones(6, 4, 7); expect r == 9, "impl 6j";
  r := Stones(3, 9, 6); expect r == 18, "impl 6k";
  r := Stones(3, 5, 7); expect r == 12, "impl 6l";
  r := Stones(5, 6, 1); expect r == 9, "impl 6m";
  r := Stones(2, 9, 1); expect r == 6, "impl 6n";
  r := Stones(0, 6, 4); expect r == 6, "impl 6o";
  r := Stones(5, 9, 1); expect r == 12, "impl 6p";
  r := Stones(6, 1, 7); expect r == 3, "impl 6q";
  r := Stones(0, 6, 10); expect r == 15, "impl 6r";
  r := Stones(2, 10, 7); expect r == 15, "impl 6s";
  r := Stones(4, 5, 10); expect r == 15, "impl 6t";

  // Test 7
  r := Stones(6, 0, 8); expect r == 0, "impl 7a";
  r := Stones(0, 6, 5); expect r == 6, "impl 7b";
  r := Stones(1, 7, 3); expect r == 6, "impl 7c";
  r := Stones(6, 5, 2); expect r == 9, "impl 7d";
  r := Stones(9, 10, 0); expect r == 15, "impl 7e";
  r := Stones(2, 8, 8); expect r == 18, "impl 7f";
  r := Stones(9, 8, 1); expect r == 12, "impl 7g";
  r := Stones(1, 9, 8); expect r == 15, "impl 7h";
  r := Stones(2, 4, 10); expect r == 12, "impl 7i";
  r := Stones(9, 5, 0); expect r == 6, "impl 7j";
  r := Stones(2, 9, 1); expect r == 6, "impl 7k";
  r := Stones(5, 5, 10); expect r == 15, "impl 7l";
  r := Stones(10, 8, 6); expect r == 15, "impl 7m";
  r := Stones(3, 6, 0); expect r == 9, "impl 7n";
  r := Stones(10, 9, 2); expect r == 15, "impl 7o";
  r := Stones(6, 9, 1); expect r == 12, "impl 7p";
  r := Stones(8, 4, 10); expect r == 12, "impl 7q";
  r := Stones(10, 3, 4); expect r == 6, "impl 7r";
  r := Stones(10, 0, 10); expect r == 0, "impl 7s";
  r := Stones(6, 1, 9); expect r == 3, "impl 7t";

  // Test 8
  r := Stones(2, 0, 8); expect r == 0, "impl 8a";
  r := Stones(8, 3, 5); expect r == 6, "impl 8b";
  r := Stones(8, 10, 3); expect r == 15, "impl 8c";
  r := Stones(3, 2, 4); expect r == 6, "impl 8d";
  r := Stones(4, 2, 1); expect r == 3, "impl 8e";
  r := Stones(0, 3, 7); expect r == 9, "impl 8f";
  r := Stones(0, 7, 5); expect r == 6, "impl 8g";
  r := Stones(7, 7, 8); expect r == 15, "impl 8h";
  r := Stones(3, 3, 9); expect r == 9, "impl 8i";
  r := Stones(1, 7, 5); expect r == 9, "impl 8j";
  r := Stones(2, 8, 4); expect r == 12, "impl 8k";
  r := Stones(6, 3, 0); expect r == 3, "impl 8l";
  r := Stones(4, 1, 10); expect r == 3, "impl 8m";
  r := Stones(3, 3, 2); expect r == 6, "impl 8n";
  r := Stones(0, 0, 0); expect r == 0, "impl 8o";
  r := Stones(7, 9, 2); expect r == 15, "impl 8p";
  r := Stones(10, 6, 1); expect r == 9, "impl 8q";
  r := Stones(10, 2, 6); expect r == 6, "impl 8r";
  r := Stones(8, 9, 1); expect r == 12, "impl 8s";
  r := Stones(8, 8, 0); expect r == 12, "impl 8t";

  print "All tests passed\n";
}
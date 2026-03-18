predicate Beautiful(ny: int, nb: int, nr: int)
{
  nb == ny + 1 && nr == nb + 1
}

predicate ValidChoice(y: int, b: int, r: int, ny: int, nb: int, nr: int)
{
  0 <= ny <= y && 0 <= nb <= b && 0 <= nr <= r && Beautiful(ny, nb, nr)
}

predicate IsMaxOrnaments(y: int, b: int, r: int, total: int)
{
  (exists ny | 0 <= ny <= y ::
    ValidChoice(y, b, r, ny, ny + 1, ny + 2) &&
    total == ny + (ny + 1) + (ny + 2))
  &&
  (forall ny | 0 <= ny <= y ::
    ValidChoice(y, b, r, ny, ny + 1, ny + 2) ==>
    ny + (ny + 1) + (ny + 2) <= total)
}

method MaxOrnaments(y: int, b: int, r: int) returns (total: int)
  requires y >= 1 && b >= 2 && r >= 3
  ensures exists ny | 0 <= ny <= y ::
    ValidChoice(y, b, r, ny, ny + 1, ny + 2) &&
    total == ny + (ny + 1) + (ny + 2)
  ensures forall ny | 0 <= ny <= y ::
    ValidChoice(y, b, r, ny, ny + 1, ny + 2) ==>
    ny + (ny + 1) + (ny + 2) <= total
{
  var m := y;
  if b - 1 < m { m := b - 1; }
  if r - 2 < m { m := r - 2; }
  total := 3 * m + 3;
}

method Main()
{
  var result: int;

  // ===== SPEC POSITIVE TESTS (small inputs, bounded quantifiers) =====
  // (y, b, r) -> correct total, verify spec accepts it
  // (1,2,3)->6, (2,3,4)->9, (3,4,5)->12, (1,5,3)->6, (3,3,3)->6
  // (2,5,5)->9, (3,5,5)->12, (1,3,4)->6, (2,2,3)->6, (3,8,5)->12
  expect IsMaxOrnaments(1, 2, 3, 6), "spec positive 1";
  expect IsMaxOrnaments(2, 3, 4, 9), "spec positive 2";
  expect IsMaxOrnaments(3, 4, 5, 12), "spec positive 3";
  expect IsMaxOrnaments(1, 5, 3, 6), "spec positive 4";
  expect IsMaxOrnaments(3, 3, 3, 6), "spec positive 5";
  expect IsMaxOrnaments(2, 5, 5, 9), "spec positive 6";
  expect IsMaxOrnaments(3, 5, 5, 12), "spec positive 7";
  expect IsMaxOrnaments(1, 3, 4, 6), "spec positive 8";
  expect IsMaxOrnaments(2, 2, 3, 6), "spec positive 9";
  expect IsMaxOrnaments(3, 8, 5, 12), "spec positive 10";

  // ===== SPEC NEGATIVE TESTS (small inputs, wrong output off by +1) =====
  expect !IsMaxOrnaments(1, 2, 3, 7), "spec negative 1";
  expect !IsMaxOrnaments(2, 3, 4, 10), "spec negative 2";
  expect !IsMaxOrnaments(3, 4, 5, 13), "spec negative 3";
  expect !IsMaxOrnaments(1, 5, 3, 7), "spec negative 4";
  expect !IsMaxOrnaments(3, 3, 3, 7), "spec negative 5";
  expect !IsMaxOrnaments(2, 5, 5, 10), "spec negative 6";
  expect !IsMaxOrnaments(3, 5, 5, 13), "spec negative 7";
  expect !IsMaxOrnaments(1, 3, 4, 7), "spec negative 8";
  expect !IsMaxOrnaments(2, 2, 3, 7), "spec negative 9";
  expect !IsMaxOrnaments(3, 8, 5, 13), "spec negative 10";

  // ===== IMPLEMENTATION TESTS (full-size inputs) =====
  result := MaxOrnaments(8, 13, 9);
  expect result == 24, "impl test 1 failed";

  result := MaxOrnaments(13, 3, 6);
  expect result == 9, "impl test 2 failed";

  result := MaxOrnaments(3, 8, 20);
  expect result == 12, "impl test 3 failed";

  result := MaxOrnaments(1, 2, 3);
  expect result == 6, "impl test 4 failed";

  result := MaxOrnaments(100, 100, 100);
  expect result == 297, "impl test 5 failed";

  result := MaxOrnaments(9, 5, 5);
  expect result == 12, "impl test 6 failed";

  result := MaxOrnaments(88, 89, 7);
  expect result == 18, "impl test 7 failed";

  result := MaxOrnaments(50, 80, 70);
  expect result == 153, "impl test 8 failed";

  result := MaxOrnaments(80, 81, 82);
  expect result == 243, "impl test 9 failed";

  result := MaxOrnaments(100, 98, 99);
  expect result == 294, "impl test 10 failed";

  print "All tests passed\n";
}
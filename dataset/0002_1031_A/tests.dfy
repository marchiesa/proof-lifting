predicate OnBorder(r: int, c: int, top: int, left: int, rows: int, cols: int)
{
  rows >= 1 && cols >= 1 &&
  top <= r < top + rows && left <= c < left + cols &&
  (r == top || r == top + rows - 1 || c == left || c == left + cols - 1)
}

predicate InRing(r: int, c: int, w: int, h: int, ring: int)
{
  OnBorder(r, c, 2 * ring, 2 * ring, h - 4 * ring, w - 4 * ring)
}

predicate IsGilded(r: int, c: int, w: int, h: int, k: int)
{
  exists i | 0 <= i < k :: InRing(r, c, w, h, i)
}

function CountGildedUpTo(w: int, h: int, k: int, n: int): int
  requires w >= 1 && h >= 1 && 0 <= n <= w * h
  decreases n
{
  if n == 0 then 0
  else
    var r := (n - 1) / w;
    var c := (n - 1) % w;
    CountGildedUpTo(w, h, k, n - 1) + (if IsGilded(r, c, w, h, k) then 1 else 0)
}

function CountGilded(w: int, h: int, k: int): int
  requires w >= 1 && h >= 1
{
  CountGildedUpTo(w, h, k, w * h)
}

method {:verify false} GoldenPlate(w: int, h: int, k: int) returns (gilded: int)
  requires w >= 1 && h >= 1 && k >= 0
  ensures gilded == CountGilded(w, h, k)
{
  gilded := 0;
  var ww := w;
  var hh := h;
  var i := 0;
  while i < k
  {
    var minWH := if ww < hh then ww else hh;
    var maxWH := if ww > hh then ww else hh;
    if minWH == 1 {
      gilded := gilded + maxWH;
    } else {
      gilded := gilded + 2 * (ww + hh) - 4;
    }
    ww := ww - 4;
    hh := hh - 4;
    i := i + 1;
  }
}

method Main()
{
  var result: int;

  // ===== SPEC POSITIVE TESTS (small inputs only) =====
  expect CountGilded(3, 3, 1) == 8, "spec positive 1";
  expect CountGilded(4, 3, 1) == 10, "spec positive 7";
  expect CountGilded(3, 4, 1) == 10, "spec positive 8";
  expect CountGilded(3, 10, 1) == 22, "spec positive 9";
  expect CountGilded(12, 3, 1) == 26, "spec positive 10";

  // ===== SPEC NEGATIVE TESTS (small inputs only) =====
  expect CountGilded(3, 3, 1) != 9, "spec negative 1";
  expect CountGilded(4, 3, 1) != 11, "spec negative 7";
  expect CountGilded(3, 4, 1) != 11, "spec negative 8";
  expect CountGilded(3, 10, 1) != 23, "spec negative 9";
  expect CountGilded(12, 3, 1) != 27, "spec negative 10";

  // ===== IMPLEMENTATION TESTS (all test pairs) =====
  result := GoldenPlate(3, 3, 1);
  expect result == 8, "impl test 1 failed";

  result := GoldenPlate(7, 9, 1);
  expect result == 28, "impl test 2 failed";

  result := GoldenPlate(7, 9, 2);
  expect result == 40, "impl test 3 failed";

  result := GoldenPlate(18, 26, 3);
  expect result == 204, "impl test 4 failed";

  result := GoldenPlate(63, 34, 8);
  expect result == 1072, "impl test 5 failed";

  result := GoldenPlate(100, 100, 25);
  expect result == 5100, "impl test 6 failed";

  result := GoldenPlate(4, 3, 1);
  expect result == 10, "impl test 7 failed";

  result := GoldenPlate(3, 4, 1);
  expect result == 10, "impl test 8 failed";

  result := GoldenPlate(3, 10, 1);
  expect result == 22, "impl test 9 failed";

  result := GoldenPlate(12, 3, 1);
  expect result == 26, "impl test 10 failed";

  print "All tests passed\n";
}
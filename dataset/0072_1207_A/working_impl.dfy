method MaxProfit(b: int, p: int, f: int, h: int, c: int) returns (profit: int)
{
  var lb := b;
  var lp := p;
  var lf := f;
  var lh := h;
  var lc := c;

  if lh < lc {
    var tmp := lh;
    lh := lc;
    lc := tmp;
    tmp := lp;
    lp := lf;
    lf := tmp;
  }

  var ham := lp;
  if lb / 2 < ham {
    ham := lb / 2;
  }
  profit := ham * lh;
  lb := lb - 2 * ham;

  var chicken := lf;
  if lb / 2 < chicken {
    chicken := lb / 2;
  }
  profit := profit + chicken * lc;
}

method Main()
{
  var result: int;

  // Test 1
  result := MaxProfit(15, 2, 3, 5, 10);
  expect result == 40, "Test 1.1 failed";

  result := MaxProfit(7, 5, 2, 10, 12);
  expect result == 34, "Test 1.2 failed";

  result := MaxProfit(1, 100, 100, 100, 100);
  expect result == 0, "Test 1.3 failed";

  // Test 2
  result := MaxProfit(1, 1, 1, 1, 1);
  expect result == 0, "Test 2.1 failed";

  result := MaxProfit(100, 100, 100, 100, 100);
  expect result == 5000, "Test 2.2 failed";

  result := MaxProfit(1, 100, 100, 100, 100);
  expect result == 0, "Test 2.3 failed";

  result := MaxProfit(100, 1, 1, 100, 100);
  expect result == 200, "Test 2.4 failed";

  result := MaxProfit(100, 50, 50, 100, 99);
  expect result == 5000, "Test 2.5 failed";

  result := MaxProfit(100, 51, 51, 100, 99);
  expect result == 5000, "Test 2.6 failed";

  result := MaxProfit(99, 51, 51, 100, 99);
  expect result == 4900, "Test 2.7 failed";

  // Test 3
  result := MaxProfit(18, 6, 4, 3, 4);
  expect result == 31, "Test 3.1 failed";

  print "All tests passed\n";
}
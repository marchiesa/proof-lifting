method RedAndBlueBeans(r: int, b: int, d: int) returns (result: bool)
{
  var rr := r;
  var bb := b;
  if rr > bb {
    var tmp := rr;
    rr := bb;
    bb := tmp;
  }
  result := rr * (d + 1) >= bb;
}

method Main()
{
  var result: bool;

  // Test 1
  result := RedAndBlueBeans(1, 1, 0);
  expect result == true, "Test 1.1: (1, 1, 0) expected YES";

  result := RedAndBlueBeans(2, 7, 3);
  expect result == true, "Test 1.2: (2, 7, 3) expected YES";

  result := RedAndBlueBeans(6, 1, 4);
  expect result == false, "Test 1.3: (6, 1, 4) expected NO";

  result := RedAndBlueBeans(5, 4, 0);
  expect result == false, "Test 1.4: (5, 4, 0) expected NO";

  // Test 2 (10 identical cases)
  result := RedAndBlueBeans(1, 1000000000, 1000000000);
  expect result == true, "Test 2: (1, 1000000000, 1000000000) expected YES";

  // Test 3 & 4 (15 identical cases)
  result := RedAndBlueBeans(1000000000, 1, 1000000000);
  expect result == true, "Test 3/4: (1000000000, 1, 1000000000) expected YES";

  // Test 5
  result := RedAndBlueBeans(1, 1, 1);
  expect result == true, "Test 5: (1, 1, 1) expected YES";

  // Test 6
  result := RedAndBlueBeans(2, 1, 1);
  expect result == true, "Test 6: (2, 1, 1) expected YES";

  // Test 7
  result := RedAndBlueBeans(150, 150, 150);
  expect result == true, "Test 7: (150, 150, 150) expected YES";

  print "All tests passed\n";
}
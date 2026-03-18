method ThreePairwiseMaximums(x: int, y: int, z: int) returns (possible: bool, a: int, b: int, c: int)
{
  var m := x;
  if y > m { m := y; }
  if z > m { m := z; }

  var cnt := 0;
  if x == m { cnt := cnt + 1; }
  if y == m { cnt := cnt + 1; }
  if z == m { cnt := cnt + 1; }

  if cnt >= 2 {
    possible := true;
    a := if x <= y then x else y;
    b := if x <= z then x else z;
    c := if y <= z then y else z;
  } else {
    possible := false;
    a := 0;
    b := 0;
    c := 0;
  }
}

function MaxOf(a: int, b: int): int {
  if a > b then a else b
}

method Main()
{
  var p: bool;
  var a: int;
  var b: int;
  var c: int;

  // Test 1, case 1: (3, 2, 3) -> YES
  p, a, b, c := ThreePairwiseMaximums(3, 2, 3);
  expect p == true, "Test 1.1: expected possible";
  expect a > 0 && b > 0 && c > 0, "Test 1.1: values must be positive";
  expect MaxOf(a, b) == 3, "Test 1.1: max(a,b) != 3";
  expect MaxOf(a, c) == 2, "Test 1.1: max(a,c) != 2";
  expect MaxOf(b, c) == 3, "Test 1.1: max(b,c) != 3";

  // Test 1, case 2: (100, 100, 100) -> YES
  p, a, b, c := ThreePairwiseMaximums(100, 100, 100);
  expect p == true, "Test 1.2: expected possible";
  expect a > 0 && b > 0 && c > 0, "Test 1.2: values must be positive";
  expect MaxOf(a, b) == 100, "Test 1.2: max(a,b) != 100";
  expect MaxOf(a, c) == 100, "Test 1.2: max(a,c) != 100";
  expect MaxOf(b, c) == 100, "Test 1.2: max(b,c) != 100";

  // Test 1, case 3: (50, 49, 49) -> NO
  p, a, b, c := ThreePairwiseMaximums(50, 49, 49);
  expect p == false, "Test 1.3: expected not possible";

  // Test 1, case 4: (10, 30, 20) -> NO
  p, a, b, c := ThreePairwiseMaximums(10, 30, 20);
  expect p == false, "Test 1.4: expected not possible";

  // Test 1, case 5: (1, 1000000000, 1000000000) -> YES
  p, a, b, c := ThreePairwiseMaximums(1, 1000000000, 1000000000);
  expect p == true, "Test 1.5: expected possible";
  expect a > 0 && b > 0 && c > 0, "Test 1.5: values must be positive";
  expect MaxOf(a, b) == 1, "Test 1.5: max(a,b) != 1";
  expect MaxOf(a, c) == 1000000000, "Test 1.5: max(a,c) != 1000000000";
  expect MaxOf(b, c) == 1000000000, "Test 1.5: max(b,c) != 1000000000";

  // Test 2, case 1: (5, 7, 7) -> YES
  p, a, b, c := ThreePairwiseMaximums(5, 7, 7);
  expect p == true, "Test 2.1: expected possible";
  expect a > 0 && b > 0 && c > 0, "Test 2.1: values must be positive";
  expect MaxOf(a, b) == 5, "Test 2.1: max(a,b) != 5";
  expect MaxOf(a, c) == 7, "Test 2.1: max(a,c) != 7";
  expect MaxOf(b, c) == 7, "Test 2.1: max(b,c) != 7";

  // Test 2, case 2: (6, 7, 3) -> NO
  p, a, b, c := ThreePairwiseMaximums(6, 7, 3);
  expect p == false, "Test 2.2: expected not possible";

  // Test 3: (127869, 127869, 127869) -> YES
  p, a, b, c := ThreePairwiseMaximums(127869, 127869, 127869);
  expect p == true, "Test 3: expected possible";
  expect a > 0 && b > 0 && c > 0, "Test 3: values must be positive";
  expect MaxOf(a, b) == 127869, "Test 3: max(a,b) != 127869";
  expect MaxOf(a, c) == 127869, "Test 3: max(a,c) != 127869";
  expect MaxOf(b, c) == 127869, "Test 3: max(b,c) != 127869";

  // Test 4: (12789, 12789, 12789) -> YES
  p, a, b, c := ThreePairwiseMaximums(12789, 12789, 12789);
  expect p == true, "Test 4: expected possible";
  expect a > 0 && b > 0 && c > 0, "Test 4: values must be positive";
  expect MaxOf(a, b) == 12789, "Test 4: max(a,b) != 12789";
  expect MaxOf(a, c) == 12789, "Test 4: max(a,c) != 12789";
  expect MaxOf(b, c) == 12789, "Test 4: max(b,c) != 12789";

  // Test 5: (78738, 78738, 78738) -> YES
  p, a, b, c := ThreePairwiseMaximums(78738, 78738, 78738);
  expect p == true, "Test 5: expected possible";
  expect a > 0 && b > 0 && c > 0, "Test 5: values must be positive";
  expect MaxOf(a, b) == 78738, "Test 5: max(a,b) != 78738";
  expect MaxOf(a, c) == 78738, "Test 5: max(a,c) != 78738";
  expect MaxOf(b, c) == 78738, "Test 5: max(b,c) != 78738";

  // Test 6: (78788, 78788, 78788) -> YES
  p, a, b, c := ThreePairwiseMaximums(78788, 78788, 78788);
  expect p == true, "Test 6: expected possible";
  expect a > 0 && b > 0 && c > 0, "Test 6: values must be positive";
  expect MaxOf(a, b) == 78788, "Test 6: max(a,b) != 78788";
  expect MaxOf(a, c) == 78788, "Test 6: max(a,c) != 78788";
  expect MaxOf(b, c) == 78788, "Test 6: max(b,c) != 78788";

  print "All tests passed\n";
}
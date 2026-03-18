method TheCakeIsALie(n: int, m: int, k: int) returns (result: bool)
{
  var remaining := k - (1 * (m - 1) + m * (n - 1));
  result := remaining == 0;
}

method Main()
{
  var r: bool;

  // Test 1
  r := TheCakeIsALie(1, 1, 0);
  expect r == true, "Failed: (1,1,0) expected YES";
  r := TheCakeIsALie(2, 2, 2);
  expect r == false, "Failed: (2,2,2) expected NO";
  r := TheCakeIsALie(2, 2, 3);
  expect r == true, "Failed: (2,2,3) expected YES";
  r := TheCakeIsALie(2, 2, 4);
  expect r == false, "Failed: (2,2,4) expected NO";
  r := TheCakeIsALie(1, 4, 3);
  expect r == true, "Failed: (1,4,3) expected YES";
  r := TheCakeIsALie(100, 100, 10000);
  expect r == false, "Failed: (100,100,10000) expected NO";

  // Test 2 (additional cases)
  r := TheCakeIsALie(3, 3, 7);
  expect r == false, "Failed: (3,3,7) expected NO";
  r := TheCakeIsALie(3, 3, 9);
  expect r == false, "Failed: (3,3,9) expected NO";
  r := TheCakeIsALie(2, 4, 8);
  expect r == false, "Failed: (2,4,8) expected NO";

  // Test 3
  r := TheCakeIsALie(1, 1, 0);
  expect r == true, "Failed: (1,1,0) expected YES [test3]";

  // Test 4
  r := TheCakeIsALie(2, 2, 2);
  expect r == false, "Failed: (2,2,2) expected NO [test4]";

  // Test 5
  r := TheCakeIsALie(1, 5, 4);
  expect r == true, "Failed: (1,5,4) expected YES";

  // Test 6
  r := TheCakeIsALie(5, 1, 4);
  expect r == true, "Failed: (5,1,4) expected YES";

  // Test 7
  r := TheCakeIsALie(3, 3, 8);
  expect r == true, "Failed: (3,3,8) expected YES";

  // Test 8
  r := TheCakeIsALie(10, 10, 100);
  expect r == false, "Failed: (10,10,100) expected NO";

  // Test 9
  r := TheCakeIsALie(1, 1, 5);
  expect r == false, "Failed: (1,1,5) expected NO";

  // Test 10
  r := TheCakeIsALie(50, 50, 2500);
  expect r == false, "Failed: (50,50,2500) expected NO";

  // Test 11
  r := TheCakeIsALie(2, 3, 5);
  expect r == true, "Failed: (2,3,5) expected YES";
  r := TheCakeIsALie(4, 4, 12);
  expect r == false, "Failed: (4,4,12) expected NO";
  r := TheCakeIsALie(1, 10, 9);
  expect r == true, "Failed: (1,10,9) expected YES";

  // Test 12
  r := TheCakeIsALie(3, 2, 4);
  expect r == false, "Failed: (3,2,4) expected NO";
  r := TheCakeIsALie(5, 5, 40);
  expect r == false, "Failed: (5,5,40) expected NO";
  r := TheCakeIsALie(1, 1, 1);
  expect r == false, "Failed: (1,1,1) expected NO";
  r := TheCakeIsALie(7, 3, 12);
  expect r == false, "Failed: (7,3,12) expected NO";
  r := TheCakeIsALie(2, 8, 9);
  expect r == false, "Failed: (2,8,9) expected NO";

  print "All tests passed\n";
}
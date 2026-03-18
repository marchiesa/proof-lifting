method MarketingScheme(l: int, r: int) returns (result: bool)
{
  result := l * 2 > r;
}

method Main()
{
  var r: bool;

  // Test 1
  r := MarketingScheme(3, 4);
  expect r == true, "Test 1.1 failed";
  r := MarketingScheme(1, 2);
  expect r == false, "Test 1.2 failed";
  r := MarketingScheme(120, 150);
  expect r == true, "Test 1.3 failed";

  // Test 2
  r := MarketingScheme(500000000, 1000000000);
  expect r == false, "Test 2.1 failed";

  // Test 3
  r := MarketingScheme(100000001, 200000002);
  expect r == false, "Test 3.1 failed";

  // Test 4
  r := MarketingScheme(1000000000, 1000000000);
  expect r == true, "Test 4.1 failed";

  // Test 5
  r := MarketingScheme(100000000, 199999999);
  expect r == true, "Test 5.1 failed";

  // Test 6
  r := MarketingScheme(500000000, 1000000000);
  expect r == false, "Test 6.1 failed";
  r := MarketingScheme(500000000, 999999999);
  expect r == true, "Test 6.2 failed";
  r := MarketingScheme(499999998, 999999996);
  expect r == false, "Test 6.3 failed";
  r := MarketingScheme(499999998, 999999995);
  expect r == true, "Test 6.4 failed";
  r := MarketingScheme(499999998, 999999997);
  expect r == false, "Test 6.5 failed";

  // Test 7
  r := MarketingScheme(50000000, 100000000);
  expect r == false, "Test 7.1 failed";
  r := MarketingScheme(50000001, 100000000);
  expect r == true, "Test 7.2 failed";
  r := MarketingScheme(50000000, 99999999);
  expect r == true, "Test 7.3 failed";
  r := MarketingScheme(49999999, 99999999);
  expect r == false, "Test 7.4 failed";

  // Test 8
  r := MarketingScheme(999999999, 1000000000);
  expect r == true, "Test 8.1 failed";

  // Test 9
  r := MarketingScheme(500000001, 1000000000);
  expect r == true, "Test 9.1 failed";
  r := MarketingScheme(500000000, 1000000000);
  expect r == false, "Test 9.2 failed";

  // Test 10
  r := MarketingScheme(10485760, 20971520);
  expect r == false, "Test 10.1 failed";

  // Test 11
  r := MarketingScheme(499999999, 999999998);
  expect r == false, "Test 11.1 failed";
  r := MarketingScheme(499999999, 999999997);
  expect r == true, "Test 11.2 failed";

  // Test 12
  r := MarketingScheme(20971520, 41943040);
  expect r == false, "Test 12.1 failed";

  // Test 13
  r := MarketingScheme(109999999, 219999998);
  expect r == false, "Test 13.1 failed";

  // Test 14
  r := MarketingScheme(500000000, 999999999);
  expect r == true, "Test 14.1 failed";

  // Test 15
  r := MarketingScheme(500000000, 1000000000);
  expect r == false, "Test 15.1 failed";
  r := MarketingScheme(101, 202);
  expect r == false, "Test 15.2 failed";
  r := MarketingScheme(102, 204);
  expect r == false, "Test 15.3 failed";
  r := MarketingScheme(102, 205);
  expect r == false, "Test 15.4 failed";
  r := MarketingScheme(500000001, 1000000000);
  expect r == true, "Test 15.5 failed";
  r := MarketingScheme(101, 200);
  expect r == true, "Test 15.6 failed";
  r := MarketingScheme(101, 201);
  expect r == true, "Test 15.7 failed";
  r := MarketingScheme(102, 203);
  expect r == true, "Test 15.8 failed";

  // Test 16
  r := MarketingScheme(54345457, 108690913);
  expect r == true, "Test 16.1 failed";

  // Test 17
  r := MarketingScheme(335544320, 671088640);
  expect r == false, "Test 17.1 failed";

  // Test 18
  r := MarketingScheme(335544321, 671088639);
  expect r == true, "Test 18.1 failed";

  // Test 19
  r := MarketingScheme(54345456, 108690913);
  expect r == false, "Test 19.1 failed";

  // Test 20
  r := MarketingScheme(335544322, 671088639);
  expect r == true, "Test 20.1 failed";

  print "All tests passed\n";
}
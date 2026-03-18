method BuyTheString(s: string, c0: int, c1: int, h: int) returns (cost: int)
{
  var ec1 := if c1 < h + c0 then c1 else h + c0;
  var ec0 := if c0 < h + ec1 then c0 else h + ec1;
  var count0 := 0;
  var count1 := 0;
  var i := 0;
  while i < |s|
  {
    if s[i] == '0' {
      count0 := count0 + 1;
    } else {
      count1 := count1 + 1;
    }
    i := i + 1;
  }
  cost := count0 * ec0 + count1 * ec1;
}

method Main()
{
  var r: int;

  // Test 1
  r := BuyTheString("100", 1, 1, 1);
  expect r == 3, "Test 1.1";
  r := BuyTheString("01010", 10, 100, 1);
  expect r == 52, "Test 1.2";
  r := BuyTheString("11111", 10, 1, 1);
  expect r == 5, "Test 1.3";
  r := BuyTheString("11111", 1, 10, 1);
  expect r == 10, "Test 1.4";
  r := BuyTheString("101110110101", 2, 1, 10);
  expect r == 16, "Test 1.5";
  r := BuyTheString("00", 100, 1, 10);
  expect r == 22, "Test 1.6";

  // Test 2
  r := BuyTheString("1000000110", 3, 1, 1);
  expect r == 17, "Test 2.1";
  r := BuyTheString("0", 10, 1, 1000);
  expect r == 10, "Test 2.2";
  r := BuyTheString("1", 1, 10, 2);
  expect r == 3, "Test 2.3";
  r := BuyTheString("1001", 4, 4, 1);
  expect r == 16, "Test 2.4";
  r := BuyTheString("1", 1, 1, 1);
  expect r == 1, "Test 2.5";
  r := BuyTheString("11", 1000, 500, 1000);
  expect r == 1000, "Test 2.6";
  r := BuyTheString("101", 500, 500, 1);
  expect r == 1500, "Test 2.7";

  // Test 3
  r := BuyTheString("101", 3, 7, 2);
  expect r == 13, "Test 3.1";
  r := BuyTheString("0000", 10, 1, 5);
  expect r == 24, "Test 3.2";
  r := BuyTheString("11", 5, 5, 1);
  expect r == 10, "Test 3.3";

  // Test 4
  r := BuyTheString("0", 1, 1, 1);
  expect r == 1, "Test 4.1";

  // Test 5
  r := BuyTheString("1", 1, 1, 1);
  expect r == 1, "Test 5.1";

  // Test 6
  r := BuyTheString("010", 10, 10, 1);
  expect r == 30, "Test 6.1";
  r := BuyTheString("110100", 2, 3, 4);
  expect r == 15, "Test 6.2";

  // Test 7
  r := BuyTheString("0101010101", 50, 50, 50);
  expect r == 500, "Test 7.1";

  // Test 8
  r := BuyTheString("0", 1, 1, 1);
  expect r == 1, "Test 8.1";
  r := BuyTheString("1", 1, 1, 1);
  expect r == 1, "Test 8.2";
  r := BuyTheString("01", 1, 1, 1);
  expect r == 2, "Test 8.3";
  r := BuyTheString("010", 1, 1, 1);
  expect r == 3, "Test 8.4";

  // Test 9
  r := BuyTheString("1100101", 3, 8, 2);
  expect r == 29, "Test 9.1";

  // Test 10
  r := BuyTheString("1111", 1, 50, 3);
  expect r == 16, "Test 10.1";
  r := BuyTheString("0000", 50, 1, 3);
  expect r == 16, "Test 10.2";

  // Test 11
  r := BuyTheString("00001111", 5, 5, 10);
  expect r == 40, "Test 11.1";

  // Test 12
  r := BuyTheString("0", 1, 1, 1);
  expect r == 1, "Test 12.1";
  r := BuyTheString("1", 1, 1, 1);
  expect r == 1, "Test 12.2";
  r := BuyTheString("0", 2, 3, 4);
  expect r == 2, "Test 12.3";
  r := BuyTheString("1", 3, 2, 4);
  expect r == 2, "Test 12.4";
  r := BuyTheString("01", 5, 5, 5);
  expect r == 10, "Test 12.5";
  r := BuyTheString("11", 1, 50, 1);
  expect r == 4, "Test 12.6";
  r := BuyTheString("000", 50, 1, 50);
  expect r == 150, "Test 12.7";
  r := BuyTheString("111", 1, 50, 1);
  expect r == 6, "Test 12.8";
  r := BuyTheString("0101", 10, 10, 1);
  expect r == 40, "Test 12.9";
  r := BuyTheString("10101", 7, 3, 2);
  expect r == 19, "Test 12.10";

  print "All tests passed\n";
}
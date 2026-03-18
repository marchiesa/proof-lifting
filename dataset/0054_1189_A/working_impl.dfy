method KeanuReeves(s: string) returns (k: int, parts: seq<string>)
{
  var zeros := 0;
  var ones := 0;
  var i := 0;
  while i < |s|
  {
    if s[i] == '0' {
      zeros := zeros + 1;
    } else {
      ones := ones + 1;
    }
    i := i + 1;
  }
  if zeros != ones {
    k := 1;
    parts := [s];
  } else {
    k := 2;
    parts := [s[..|s| - 1], [s[|s| - 1]]];
  }
}

method Main()
{
  var k: int;
  var parts: seq<string>;

  // Test 1
  k, parts := KeanuReeves("1");
  expect k == 1, "Test 1: k";
  expect parts == ["1"], "Test 1: parts";

  // Test 2
  k, parts := KeanuReeves("10");
  expect k == 2, "Test 2: k";
  expect parts == ["1", "0"], "Test 2: parts";

  // Test 3
  k, parts := KeanuReeves("100011");
  expect k == 2, "Test 3: k";
  expect parts == ["10001", "1"], "Test 3: parts";

  // Test 4
  k, parts := KeanuReeves("0101");
  expect k == 2, "Test 4: k";
  expect parts == ["010", "1"], "Test 4: parts";

  // Test 5
  k, parts := KeanuReeves("1101001100");
  expect k == 2, "Test 5: k";
  expect parts == ["110100110", "0"], "Test 5: parts";

  // Test 6
  k, parts := KeanuReeves("10010000111011010000111011111010010100001101");
  expect k == 2, "Test 6: k";
  expect parts == ["1001000011101101000011101111101001010000110", "1"], "Test 6: parts";

  // Test 7
  k, parts := KeanuReeves("01110111110010110111011110101000110110000111000100111000000101001011111000110011");
  expect k == 1, "Test 7: k";
  expect parts == ["01110111110010110111011110101000110110000111000100111000000101001011111000110011"], "Test 7: parts";

  // Test 8
  k, parts := KeanuReeves("0010110000001111110111101011100111101000110011011100100011110001101110000001000010100001011011110001");
  expect k == 2, "Test 8: k";
  expect parts == ["001011000000111111011110101110011110100011001101110010001111000110111000000100001010000101101111000", "1"], "Test 8: parts";

  // Test 9
  k, parts := KeanuReeves("010011");
  expect k == 2, "Test 9: k";
  expect parts == ["01001", "1"], "Test 9: parts";

  // Test 10
  k, parts := KeanuReeves("1100010011");
  expect k == 2, "Test 10: k";
  expect parts == ["110001001", "1"], "Test 10: parts";

  // Test 11
  k, parts := KeanuReeves("101010100101");
  expect k == 2, "Test 11: k";
  expect parts == ["10101010010", "1"], "Test 11: parts";

  // Test 12
  k, parts := KeanuReeves("110001101000101");
  expect k == 1, "Test 12: k";
  expect parts == ["110001101000101"], "Test 12: parts";

  // Test 13
  k, parts := KeanuReeves("101111001111000110");
  expect k == 1, "Test 13: k";
  expect parts == ["101111001111000110"], "Test 13: parts";

  // Test 14
  k, parts := KeanuReeves("10010000010111010111");
  expect k == 2, "Test 14: k";
  expect parts == ["1001000001011101011", "1"], "Test 14: parts";

  // Test 15
  k, parts := KeanuReeves("111100110011010001010010100011001101");
  expect k == 2, "Test 15: k";
  expect parts == ["11110011001101000101001010001100110", "1"], "Test 15: parts";

  // Test 16
  k, parts := KeanuReeves("101001101111010010111100000111111010111001001");
  expect k == 1, "Test 16: k";
  expect parts == ["101001101111010010111100000111111010111001001"], "Test 16: parts";

  // Test 17
  k, parts := KeanuReeves("111101100111001110000000100010100000011011100110001010111010101011111100");
  expect k == 2, "Test 17: k";
  expect parts == ["11110110011100111000000010001010000001101110011000101011101010101111110", "0"], "Test 17: parts";

  // Test 18
  k, parts := KeanuReeves("0110110011011111001110000110010010000111111001100001011101101000001011001101100111011111100111101110");
  expect k == 1, "Test 18: k";
  expect parts == ["0110110011011111001110000110010010000111111001100001011101101000001011001101100111011111100111101110"], "Test 18: parts";

  // Test 19
  k, parts := KeanuReeves("11");
  expect k == 1, "Test 19: k";
  expect parts == ["11"], "Test 19: parts";

  // Test 20
  k, parts := KeanuReeves("100");
  expect k == 1, "Test 20: k";
  expect parts == ["100"], "Test 20: parts";

  print "All tests passed\n";
}
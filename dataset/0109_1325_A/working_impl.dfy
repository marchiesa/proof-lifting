method EhAbAndGcd(x: int) returns (a: int, b: int)
{
  a := 1;
  b := x - 1;
}

method Main()
{
  var inputs: seq<int> := [
    2, 14,
    3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 15, 16, 17, 18, 19, 20,
    21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36,
    37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52,
    53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68,
    69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84,
    85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100,
    101, 102, 103
  ];

  var expectedAs: seq<int> := [
    1, 1,
    1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
    1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
    1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
    1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
    1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
    1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
    1, 1, 1
  ];

  var expectedBs: seq<int> := [
    1, 13,
    2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 14, 15, 16, 17, 18, 19,
    20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35,
    36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51,
    52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67,
    68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83,
    84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99,
    100, 101, 102
  ];

  var i := 0;
  while i < |inputs|
  {
    var a, b := EhAbAndGcd(inputs[i]);
    var inputStr := IntToString(inputs[i]);
    expect a == expectedAs[i], "Wrong a for input " + inputStr;
    expect b == expectedBs[i], "Wrong b for input " + inputStr;
    i := i + 1;
  }

  print "All tests passed\n";
}

method IntToString(n: int) returns (s: string)
{
  if n < 0 {
    var pos := IntToString(-n);
    s := "-" + pos;
  } else if n == 0 {
    s := "0";
  } else {
    s := "";
    var remaining := n;
    while remaining > 0
    {
      var digit := remaining % 10;
      s := [('0' as int + digit) as char] + s;
      remaining := remaining / 10;
    }
  }
}
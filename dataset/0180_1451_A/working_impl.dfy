method SubtractOrDivide(n: int) returns (moves: int)
{
  if n == 1 {
    return 0;
  } else if n == 2 {
    return 1;
  } else if n % 2 == 0 || n == 3 {
    return 2;
  } else {
    return 3;
  }
}

method Main()
{
  var r1 := SubtractOrDivide(1);
  var s1 := ToString(r1);
  expect r1 == 0, "n=1: expected 0, got " + s1;

  var r2 := SubtractOrDivide(2);
  var s2 := ToString(r2);
  expect r2 == 1, "n=2: expected 1, got " + s2;

  var r3 := SubtractOrDivide(3);
  var s3 := ToString(r3);
  expect r3 == 2, "n=3: expected 2, got " + s3;

  var r4 := SubtractOrDivide(4);
  var s4 := ToString(r4);
  expect r4 == 2, "n=4: expected 2, got " + s4;

  var r5 := SubtractOrDivide(6);
  var s5 := ToString(r5);
  expect r5 == 2, "n=6: expected 2, got " + s5;

  var r6 := SubtractOrDivide(9);
  var s6 := ToString(r6);
  expect r6 == 3, "n=9: expected 3, got " + s6;

  var r7 := SubtractOrDivide(10);
  var s7 := ToString(r7);
  expect r7 == 2, "n=10: expected 2, got " + s7;

  var r8 := SubtractOrDivide(25);
  var s8 := ToString(r8);
  expect r8 == 3, "n=25: expected 3, got " + s8;

  var r9 := SubtractOrDivide(49);
  var s9 := ToString(r9);
  expect r9 == 3, "n=49: expected 3, got " + s9;

  print "All tests passed\n";
}

method ToString(n: int) returns (s: string)
{
  if n < 0 {
    var pos := ToString(-n);
    return "-" + pos;
  }
  if n < 10 {
    var digits := ['0', '1', '2', '3', '4', '5', '6', '7', '8', '9'];
    return [digits[n]];
  }
  var rest := ToString(n / 10);
  var digits := ['0', '1', '2', '3', '4', '5', '6', '7', '8', '9'];
  return rest + [digits[n % 10]];
}
// Fast Exponentiation -- Runtime spec tests

function Power(base: int, exp: nat): int
{
  if exp == 0 then 1
  else base * Power(base, exp - 1)
}

method Main() {
  // Known powers
  expect Power(2, 0) == 1, "2^0 = 1";
  expect Power(2, 1) == 2, "2^1 = 2";
  expect Power(2, 10) == 1024, "2^10 = 1024";
  expect Power(3, 3) == 27, "3^3 = 27";
  expect Power(5, 0) == 1, "5^0 = 1";
  expect Power(7, 1) == 7, "7^1 = 7";
  expect Power(1, 100) == 1, "1^100 = 1";
  expect Power(0, 5) == 0, "0^5 = 0";

  // Negative base
  expect Power(-2, 3) == -8, "(-2)^3 = -8";
  expect Power(-2, 2) == 4, "(-2)^2 = 4";
  expect Power(-1, 0) == 1, "(-1)^0 = 1";

  // Wrong answers
  expect Power(2, 10) != 1023, "2^10 is not 1023";
  expect Power(3, 3) != 9, "3^3 is not 9";

  print "All spec tests passed\n";
}

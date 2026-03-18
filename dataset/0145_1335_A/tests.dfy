predicate ValidDistribution(n: int, a: int, b: int) {
  a > 0 && b > 0 && a > b && a + b == n
}

function CountDistributions(n: int, hi: int): int
  requires hi >= 0
  decreases hi
{
  if hi < 1 then 0
  else CountDistributions(n, hi - 1) + (if ValidDistribution(n, n - hi, hi) then 1 else 0)
}

method Candies(n: int) returns (ways: int)
  requires n >= 1
  ensures ways == CountDistributions(n, n - 1)
{
  if n <= 2 {
    ways := 0;
  } else {
    ways := (n - 1) / 2;
  }
}

method Main()
{
  // =============================================
  // SPEC POSITIVE TESTS
  // =============================================
  // ensures: ways == CountDistributions(n, n - 1)
  // Small inputs only (n <= 10) to keep recursion tractable

  // From Positive Test 1 (n=7->3, n=1->0, n=2->0, n=3->1; skip 2000000000, 763243547)
  expect CountDistributions(7, 6) == 3, "spec positive 1a";
  expect CountDistributions(1, 0) == 0, "spec positive 1b";
  expect CountDistributions(2, 1) == 0, "spec positive 1c";
  expect CountDistributions(3, 2) == 1, "spec positive 1d";

  // From Positive Test 2 (n=1->0, n=2->0)
  expect CountDistributions(1, 0) == 0, "spec positive 2a";
  expect CountDistributions(2, 1) == 0, "spec positive 2b";

  // Positive Test 3 skipped (n=108139 too large for recursive spec)

  // From Positive Test 4 (n=1->0, five times; representative)
  expect CountDistributions(1, 0) == 0, "spec positive 4";

  // From Positive Test 5 (n=1->0, 39 times; representative)
  expect CountDistributions(1, 0) == 0, "spec positive 5";

  // Positive Test 6 skipped (n=121112422 too large)
  // Positive Test 7 skipped (n=1411 too large)

  // From Positive Test 8 (small values only)
  expect CountDistributions(2, 1) == 0, "spec positive 8a";
  expect CountDistributions(3, 2) == 1, "spec positive 8b";
  expect CountDistributions(5, 4) == 2, "spec positive 8c";
  expect CountDistributions(7, 6) == 3, "spec positive 8d";
  expect CountDistributions(9, 8) == 4, "spec positive 8e";
  expect CountDistributions(8, 7) == 3, "spec positive 8f";
  expect CountDistributions(6, 5) == 2, "spec positive 8g";
  expect CountDistributions(4, 3) == 1, "spec positive 8h";
  expect CountDistributions(10, 9) == 4, "spec positive 8i";
  expect CountDistributions(1, 0) == 0, "spec positive 8j";

  // From Positive Test 9 (small values: n=7,1,2,3; skip 2000000000, 763243547)
  expect CountDistributions(7, 6) == 3, "spec positive 9a";
  expect CountDistributions(1, 0) == 0, "spec positive 9b";
  expect CountDistributions(2, 1) == 0, "spec positive 9c";
  expect CountDistributions(3, 2) == 1, "spec positive 9d";

  // From Positive Test 10 (n=1..10)
  expect CountDistributions(1, 0) == 0, "spec positive 10a";
  expect CountDistributions(2, 1) == 0, "spec positive 10b";
  expect CountDistributions(3, 2) == 1, "spec positive 10c";
  expect CountDistributions(4, 3) == 1, "spec positive 10d";
  expect CountDistributions(5, 4) == 2, "spec positive 10e";
  expect CountDistributions(6, 5) == 2, "spec positive 10f";
  expect CountDistributions(7, 6) == 3, "spec positive 10g";
  expect CountDistributions(8, 7) == 3, "spec positive 10h";
  expect CountDistributions(9, 8) == 4, "spec positive 10i";
  expect CountDistributions(10, 9) == 4, "spec positive 10j";

  // Positive Test 11 skipped (all values 14-970, too large for recursive spec)

  // From Positive Test 12 (n=1->0)
  expect CountDistributions(1, 0) == 0, "spec positive 12";

  // From Positive Test 13 (n=10->4)
  expect CountDistributions(10, 9) == 4, "spec positive 13";

  // From Positive Test 14 (n=1->0, n=7->3, n=2->0, n=3->1; skip large)
  expect CountDistributions(1, 0) == 0, "spec positive 14a";
  expect CountDistributions(7, 6) == 3, "spec positive 14b";
  expect CountDistributions(2, 1) == 0, "spec positive 14c";
  expect CountDistributions(3, 2) == 1, "spec positive 14d";

  // From Positive Test 15 (n=3->1, n=4->1, n=5->2)
  expect CountDistributions(3, 2) == 1, "spec positive 15a";
  expect CountDistributions(4, 3) == 1, "spec positive 15b";
  expect CountDistributions(5, 4) == 2, "spec positive 15c";

  // From Positive Test 16 (n=1..10)
  expect CountDistributions(1, 0) == 0, "spec positive 16a";
  expect CountDistributions(2, 1) == 0, "spec positive 16b";
  expect CountDistributions(3, 2) == 1, "spec positive 16c";
  expect CountDistributions(4, 3) == 1, "spec positive 16d";
  expect CountDistributions(5, 4) == 2, "spec positive 16e";
  expect CountDistributions(6, 5) == 2, "spec positive 16f";
  expect CountDistributions(7, 6) == 3, "spec positive 16g";
  expect CountDistributions(8, 7) == 3, "spec positive 16h";
  expect CountDistributions(9, 8) == 4, "spec positive 16i";
  expect CountDistributions(10, 9) == 4, "spec positive 16j";

  // Positive Tests 17-20 skipped (n=54331-54335 too large)

  // =============================================
  // SPEC NEGATIVE TESTS
  // =============================================
  // Testing: CountDistributions(n, n-1) != wrong_output
  // Small inputs from each negative pair (skip large n)

  // Negative 1: n=7, wrong=4 (correct=3)
  expect CountDistributions(7, 6) != 4, "spec negative 1";

  // Negative 2: n=1, wrong=1 (correct=0)
  expect CountDistributions(1, 0) != 1, "spec negative 2";

  // Negative 3 skipped (n=108139 too large)

  // Negative 4: n=1, wrong=1 (correct=0)
  expect CountDistributions(1, 0) != 1, "spec negative 4";

  // Negative 5: n=1, wrong=1 (correct=0)
  expect CountDistributions(1, 0) != 1, "spec negative 5";

  // Negative 6 skipped (n=121112422 too large)
  // Negative 7 skipped (n=1411 too large)

  // Negative 8: n=2, wrong=1 (correct=0)
  expect CountDistributions(2, 1) != 1, "spec negative 8";

  // Negative 9: n=7, wrong=4 (correct=3)
  expect CountDistributions(7, 6) != 4, "spec negative 9";

  // Negative 10: n=1, wrong=1 (correct=0)
  expect CountDistributions(1, 0) != 1, "spec negative 10";

  // =============================================
  // IMPLEMENTATION TESTS
  // =============================================
  var r: int;

  // Test 1
  r := Candies(7); expect r == 3, "impl test 1.1";
  r := Candies(1); expect r == 0, "impl test 1.2";
  r := Candies(2); expect r == 0, "impl test 1.3";
  r := Candies(3); expect r == 1, "impl test 1.4";
  r := Candies(2000000000); expect r == 999999999, "impl test 1.5";
  r := Candies(763243547); expect r == 381621773, "impl test 1.6";

  // Test 2
  r := Candies(1); expect r == 0, "impl test 2.1";
  r := Candies(2); expect r == 0, "impl test 2.2";

  // Test 3
  r := Candies(108139); expect r == 54069, "impl test 3.1";

  // Test 4
  r := Candies(1); expect r == 0, "impl test 4.1";
  r := Candies(1); expect r == 0, "impl test 4.2";
  r := Candies(1); expect r == 0, "impl test 4.3";
  r := Candies(1); expect r == 0, "impl test 4.4";
  r := Candies(1); expect r == 0, "impl test 4.5";

  // Test 5
  r := Candies(1); expect r == 0, "impl test 5.1";
  r := Candies(1); expect r == 0, "impl test 5.2";
  r := Candies(1); expect r == 0, "impl test 5.3";
  r := Candies(1); expect r == 0, "impl test 5.4";
  r := Candies(1); expect r == 0, "impl test 5.5";
  r := Candies(1); expect r == 0, "impl test 5.6";
  r := Candies(1); expect r == 0, "impl test 5.7";
  r := Candies(1); expect r == 0, "impl test 5.8";
  r := Candies(1); expect r == 0, "impl test 5.9";
  r := Candies(1); expect r == 0, "impl test 5.10";
  r := Candies(1); expect r == 0, "impl test 5.11";
  r := Candies(1); expect r == 0, "impl test 5.12";
  r := Candies(1); expect r == 0, "impl test 5.13";
  r := Candies(1); expect r == 0, "impl test 5.14";
  r := Candies(1); expect r == 0, "impl test 5.15";
  r := Candies(1); expect r == 0, "impl test 5.16";
  r := Candies(1); expect r == 0, "impl test 5.17";
  r := Candies(1); expect r == 0, "impl test 5.18";
  r := Candies(1); expect r == 0, "impl test 5.19";
  r := Candies(1); expect r == 0, "impl test 5.20";
  r := Candies(1); expect r == 0, "impl test 5.21";
  r := Candies(1); expect r == 0, "impl test 5.22";
  r := Candies(1); expect r == 0, "impl test 5.23";
  r := Candies(1); expect r == 0, "impl test 5.24";
  r := Candies(1); expect r == 0, "impl test 5.25";
  r := Candies(1); expect r == 0, "impl test 5.26";
  r := Candies(1); expect r == 0, "impl test 5.27";
  r := Candies(1); expect r == 0, "impl test 5.28";
  r := Candies(1); expect r == 0, "impl test 5.29";
  r := Candies(1); expect r == 0, "impl test 5.30";
  r := Candies(1); expect r == 0, "impl test 5.31";
  r := Candies(1); expect r == 0, "impl test 5.32";
  r := Candies(1); expect r == 0, "impl test 5.33";
  r := Candies(1); expect r == 0, "impl test 5.34";
  r := Candies(1); expect r == 0, "impl test 5.35";
  r := Candies(1); expect r == 0, "impl test 5.36";
  r := Candies(1); expect r == 0, "impl test 5.37";
  r := Candies(1); expect r == 0, "impl test 5.38";
  r := Candies(1); expect r == 0, "impl test 5.39";

  // Test 6
  r := Candies(121112422); expect r == 60556210, "impl test 6.1";

  // Test 7
  r := Candies(1411); expect r == 705, "impl test 7.1";

  // Test 8
  r := Candies(2); expect r == 0, "impl test 8.1";
  r := Candies(3); expect r == 1, "impl test 8.2";
  r := Candies(5); expect r == 2, "impl test 8.3";
  r := Candies(7); expect r == 3, "impl test 8.4";
  r := Candies(9); expect r == 4, "impl test 8.5";
  r := Candies(8); expect r == 3, "impl test 8.6";
  r := Candies(6); expect r == 2, "impl test 8.7";
  r := Candies(5); expect r == 2, "impl test 8.8";
  r := Candies(4); expect r == 1, "impl test 8.9";
  r := Candies(4); expect r == 1, "impl test 8.10";
  r := Candies(9); expect r == 4, "impl test 8.11";
  r := Candies(4); expect r == 1, "impl test 8.12";
  r := Candies(5); expect r == 2, "impl test 8.13";
  r := Candies(6); expect r == 2, "impl test 8.14";
  r := Candies(8); expect r == 3, "impl test 8.15";
  r := Candies(1); expect r == 0, "impl test 8.16";
  r := Candies(5); expect r == 2, "impl test 8.17";
  r := Candies(4); expect r == 1, "impl test 8.18";
  r := Candies(3); expect r == 1, "impl test 8.19";
  r := Candies(10); expect r == 4, "impl test 8.20";
  r := Candies(7); expect r == 3, "impl test 8.21";
  r := Candies(1); expect r == 0, "impl test 8.22";
  r := Candies(1); expect r == 0, "impl test 8.23";
  r := Candies(4); expect r == 1, "impl test 8.24";
  r := Candies(3); expect r == 1, "impl test 8.25";
  r := Candies(5); expect r == 2, "impl test 8.26";
  r := Candies(6); expect r == 2, "impl test 8.27";
  r := Candies(2); expect r == 0, "impl test 8.28";
  r := Candies(5); expect r == 2, "impl test 8.29";
  r := Candies(9); expect r == 4, "impl test 8.30";
  r := Candies(9); expect r == 4, "impl test 8.31";
  r := Candies(6); expect r == 2, "impl test 8.32";
  r := Candies(6); expect r == 2, "impl test 8.33";
  r := Candies(4); expect r == 1, "impl test 8.34";
  r := Candies(5); expect r == 2, "impl test 8.35";
  r := Candies(3); expect r == 1, "impl test 8.36";
  r := Candies(10); expect r == 4, "impl test 8.37";
  r := Candies(10); expect r == 4, "impl test 8.38";
  r := Candies(1); expect r == 0, "impl test 8.39";

  // Test 9
  r := Candies(7); expect r == 3, "impl test 9.1";
  r := Candies(1); expect r == 0, "impl test 9.2";
  r := Candies(2); expect r == 0, "impl test 9.3";
  r := Candies(3); expect r == 1, "impl test 9.4";
  r := Candies(2000000000); expect r == 999999999, "impl test 9.5";
  r := Candies(763243547); expect r == 381621773, "impl test 9.6";
  r := Candies(7); expect r == 3, "impl test 9.7";
  r := Candies(1); expect r == 0, "impl test 9.8";
  r := Candies(2); expect r == 0, "impl test 9.9";
  r := Candies(3); expect r == 1, "impl test 9.10";
  r := Candies(2000000000); expect r == 999999999, "impl test 9.11";
  r := Candies(763243547); expect r == 381621773, "impl test 9.12";
  r := Candies(7); expect r == 3, "impl test 9.13";
  r := Candies(1); expect r == 0, "impl test 9.14";
  r := Candies(2); expect r == 0, "impl test 9.15";
  r := Candies(3); expect r == 1, "impl test 9.16";
  r := Candies(2000000000); expect r == 999999999, "impl test 9.17";
  r := Candies(763243547); expect r == 381621773, "impl test 9.18";
  r := Candies(7); expect r == 3, "impl test 9.19";
  r := Candies(1); expect r == 0, "impl test 9.20";
  r := Candies(2); expect r == 0, "impl test 9.21";
  r := Candies(3); expect r == 1, "impl test 9.22";
  r := Candies(2000000000); expect r == 999999999, "impl test 9.23";
  r := Candies(763243547); expect r == 381621773, "impl test 9.24";
  r := Candies(7); expect r == 3, "impl test 9.25";
  r := Candies(1); expect r == 0, "impl test 9.26";
  r := Candies(2); expect r == 0, "impl test 9.27";
  r := Candies(3); expect r == 1, "impl test 9.28";
  r := Candies(2000000000); expect r == 999999999, "impl test 9.29";
  r := Candies(763243547); expect r == 381621773, "impl test 9.30";
  r := Candies(7); expect r == 3, "impl test 9.31";
  r := Candies(1); expect r == 0, "impl test 9.32";
  r := Candies(2); expect r == 0, "impl test 9.33";
  r := Candies(3); expect r == 1, "impl test 9.34";
  r := Candies(2000000000); expect r == 999999999, "impl test 9.35";
  r := Candies(763243547); expect r == 381621773, "impl test 9.36";
  r := Candies(7); expect r == 3, "impl test 9.37";
  r := Candies(1); expect r == 0, "impl test 9.38";
  r := Candies(2); expect r == 0, "impl test 9.39";

  // Test 10
  r := Candies(1); expect r == 0, "impl test 10.1";
  r := Candies(2); expect r == 0, "impl test 10.2";
  r := Candies(3); expect r == 1, "impl test 10.3";
  r := Candies(4); expect r == 1, "impl test 10.4";
  r := Candies(5); expect r == 2, "impl test 10.5";
  r := Candies(6); expect r == 2, "impl test 10.6";
  r := Candies(7); expect r == 3, "impl test 10.7";
  r := Candies(8); expect r == 3, "impl test 10.8";
  r := Candies(9); expect r == 4, "impl test 10.9";
  r := Candies(10); expect r == 4, "impl test 10.10";
  r := Candies(11); expect r == 5, "impl test 10.11";
  r := Candies(12); expect r == 5, "impl test 10.12";
  r := Candies(13); expect r == 6, "impl test 10.13";
  r := Candies(14); expect r == 6, "impl test 10.14";
  r := Candies(15); expect r == 7, "impl test 10.15";
  r := Candies(16); expect r == 7, "impl test 10.16";
  r := Candies(17); expect r == 8, "impl test 10.17";
  r := Candies(18); expect r == 8, "impl test 10.18";
  r := Candies(19); expect r == 9, "impl test 10.19";
  r := Candies(20); expect r == 9, "impl test 10.20";
  r := Candies(21); expect r == 10, "impl test 10.21";
  r := Candies(22); expect r == 10, "impl test 10.22";
  r := Candies(23); expect r == 11, "impl test 10.23";
  r := Candies(24); expect r == 11, "impl test 10.24";
  r := Candies(25); expect r == 12, "impl test 10.25";
  r := Candies(26); expect r == 12, "impl test 10.26";
  r := Candies(27); expect r == 13, "impl test 10.27";
  r := Candies(28); expect r == 13, "impl test 10.28";
  r := Candies(29); expect r == 14, "impl test 10.29";
  r := Candies(30); expect r == 14, "impl test 10.30";
  r := Candies(31); expect r == 15, "impl test 10.31";
  r := Candies(32); expect r == 15, "impl test 10.32";
  r := Candies(32); expect r == 15, "impl test 10.33";
  r := Candies(34); expect r == 16, "impl test 10.34";
  r := Candies(35); expect r == 17, "impl test 10.35";
  r := Candies(36); expect r == 17, "impl test 10.36";
  r := Candies(37); expect r == 18, "impl test 10.37";
  r := Candies(35); expect r == 17, "impl test 10.38";
  r := Candies(39); expect r == 19, "impl test 10.39";

  // Test 11
  r := Candies(710); expect r == 354, "impl test 11.1";
  r := Candies(896); expect r == 447, "impl test 11.2";
  r := Candies(635); expect r == 317, "impl test 11.3";
  r := Candies(909); expect r == 454, "impl test 11.4";
  r := Candies(528); expect r == 263, "impl test 11.5";
  r := Candies(799); expect r == 399, "impl test 11.6";
  r := Candies(184); expect r == 91, "impl test 11.7";
  r := Candies(970); expect r == 484, "impl test 11.8";
  r := Candies(731); expect r == 365, "impl test 11.9";
  r := Candies(285); expect r == 142, "impl test 11.10";
  r := Candies(481); expect r == 240, "impl test 11.11";
  r := Candies(62); expect r == 30, "impl test 11.12";
  r := Candies(829); expect r == 414, "impl test 11.13";
  r := Candies(815); expect r == 407, "impl test 11.14";
  r := Candies(204); expect r == 101, "impl test 11.15";
  r := Candies(927); expect r == 463, "impl test 11.16";
  r := Candies(48); expect r == 23, "impl test 11.17";
  r := Candies(958); expect r == 478, "impl test 11.18";
  r := Candies(858); expect r == 428, "impl test 11.19";
  r := Candies(549); expect r == 274, "impl test 11.20";
  r := Candies(722); expect r == 360, "impl test 11.21";
  r := Candies(900); expect r == 449, "impl test 11.22";
  r := Candies(290); expect r == 144, "impl test 11.23";
  r := Candies(96); expect r == 47, "impl test 11.24";
  r := Candies(414); expect r == 206, "impl test 11.25";
  r := Candies(323); expect r == 161, "impl test 11.26";
  r := Candies(488); expect r == 243, "impl test 11.27";
  r := Candies(140); expect r == 69, "impl test 11.28";
  r := Candies(494); expect r == 246, "impl test 11.29";
  r := Candies(286); expect r == 142, "impl test 11.30";
  r := Candies(783); expect r == 391, "impl test 11.31";
  r := Candies(551); expect r == 275, "impl test 11.32";
  r := Candies(896); expect r == 447, "impl test 11.33";
  r := Candies(580); expect r == 289, "impl test 11.34";
  r := Candies(724); expect r == 361, "impl test 11.35";
  r := Candies(766); expect r == 382, "impl test 11.36";
  r := Candies(841); expect r == 420, "impl test 11.37";
  r := Candies(914); expect r == 456, "impl test 11.38";
  r := Candies(200); expect r == 99, "impl test 11.39";
  r := Candies(170); expect r == 84, "impl test 11.40";
  r := Candies(384); expect r == 191, "impl test 11.41";
  r := Candies(664); expect r == 331, "impl test 11.42";
  r := Candies(14); expect r == 6, "impl test 11.43";
  r := Candies(203); expect r == 101, "impl test 11.44";
  r := Candies(582); expect r == 290, "impl test 11.45";
  r := Candies(203); expect r == 101, "impl test 11.46";
  r := Candies(678); expect r == 338, "impl test 11.47";
  r := Candies(502); expect r == 250, "impl test 11.48";
  r := Candies(677); expect r == 338, "impl test 11.49";
  r := Candies(318); expect r == 158, "impl test 11.50";
  r := Candies(189); expect r == 94, "impl test 11.51";
  r := Candies(144); expect r == 71, "impl test 11.52";
  r := Candies(97); expect r == 48, "impl test 11.53";
  r := Candies(330); expect r == 164, "impl test 11.54";
  r := Candies(169); expect r == 84, "impl test 11.55";
  r := Candies(20); expect r == 9, "impl test 11.56";
  r := Candies(492); expect r == 245, "impl test 11.57";
  r := Candies(233); expect r == 116, "impl test 11.58";
  r := Candies(198); expect r == 98, "impl test 11.59";
  r := Candies(876); expect r == 437, "impl test 11.60";
  r := Candies(697); expect r == 348, "impl test 11.61";
  r := Candies(624); expect r == 311, "impl test 11.62";
  r := Candies(877); expect r == 438, "impl test 11.63";
  r := Candies(514); expect r == 256, "impl test 11.64";
  r := Candies(828); expect r == 413, "impl test 11.65";
  r := Candies(41); expect r == 20, "impl test 11.66";
  r := Candies(575); expect r == 287, "impl test 11.67";
  r := Candies(959); expect r == 479, "impl test 11.68";
  r := Candies(499); expect r == 249, "impl test 11.69";
  r := Candies(786); expect r == 392, "impl test 11.70";
  r := Candies(621); expect r == 310, "impl test 11.71";
  r := Candies(878); expect r == 438, "impl test 11.72";
  r := Candies(547); expect r == 273, "impl test 11.73";
  r := Candies(409); expect r == 204, "impl test 11.74";
  r := Candies(194); expect r == 96, "impl test 11.75";
  r := Candies(59); expect r == 29, "impl test 11.76";
  r := Candies(657); expect r == 328, "impl test 11.77";
  r := Candies(893); expect r == 446, "impl test 11.78";
  r := Candies(230); expect r == 114, "impl test 11.79";
  r := Candies(559); expect r == 279, "impl test 11.80";
  r := Candies(170); expect r == 84, "impl test 11.81";
  r := Candies(238); expect r == 118, "impl test 11.82";
  r := Candies(752); expect r == 375, "impl test 11.83";
  r := Candies(854); expect r == 426, "impl test 11.84";
  r := Candies(385); expect r == 192, "impl test 11.85";
  r := Candies(365); expect r == 182, "impl test 11.86";
  r := Candies(415); expect r == 207, "impl test 11.87";
  r := Candies(505); expect r == 252, "impl test 11.88";
  r := Candies(584); expect r == 291, "impl test 11.89";
  r := Candies(434); expect r == 216, "impl test 11.90";
  r := Candies(135); expect r == 67, "impl test 11.91";
  r := Candies(136); expect r == 67, "impl test 11.92";
  r := Candies(610); expect r == 304, "impl test 11.93";
  r := Candies(525); expect r == 262, "impl test 11.94";
  r := Candies(945); expect r == 472, "impl test 11.95";
  r := Candies(889); expect r == 444, "impl test 11.96";
  r := Candies(941); expect r == 470, "impl test 11.97";
  r := Candies(579); expect r == 289, "impl test 11.98";

  // Test 12
  r := Candies(1); expect r == 0, "impl test 12.1";
  r := Candies(1); expect r == 0, "impl test 12.2";
  r := Candies(1); expect r == 0, "impl test 12.3";

  // Test 13
  r := Candies(10); expect r == 4, "impl test 13.1";

  // Test 14
  r := Candies(1); expect r == 0, "impl test 14.1";
  r := Candies(7); expect r == 3, "impl test 14.2";
  r := Candies(1); expect r == 0, "impl test 14.3";
  r := Candies(2); expect r == 0, "impl test 14.4";
  r := Candies(3); expect r == 1, "impl test 14.5";
  r := Candies(2000000000); expect r == 999999999, "impl test 14.6";
  r := Candies(763243547); expect r == 381621773, "impl test 14.7";

  // Test 15
  r := Candies(3); expect r == 1, "impl test 15.1";
  r := Candies(4); expect r == 1, "impl test 15.2";
  r := Candies(5); expect r == 2, "impl test 15.3";

  // Test 16
  r := Candies(1); expect r == 0, "impl test 16.1";
  r := Candies(2); expect r == 0, "impl test 16.2";
  r := Candies(3); expect r == 1, "impl test 16.3";
  r := Candies(4); expect r == 1, "impl test 16.4";
  r := Candies(5); expect r == 2, "impl test 16.5";
  r := Candies(6); expect r == 2, "impl test 16.6";
  r := Candies(7); expect r == 3, "impl test 16.7";
  r := Candies(8); expect r == 3, "impl test 16.8";
  r := Candies(9); expect r == 4, "impl test 16.9";
  r := Candies(10); expect r == 4, "impl test 16.10";
  r := Candies(11); expect r == 5, "impl test 16.11";
  r := Candies(12); expect r == 5, "impl test 16.12";
  r := Candies(13); expect r == 6, "impl test 16.13";
  r := Candies(14); expect r == 6, "impl test 16.14";
  r := Candies(15); expect r == 7, "impl test 16.15";
  r := Candies(16); expect r == 7, "impl test 16.16";
  r := Candies(17); expect r == 8, "impl test 16.17";
  r := Candies(18); expect r == 8, "impl test 16.18";
  r := Candies(19); expect r == 9, "impl test 16.19";
  r := Candies(20); expect r == 9, "impl test 16.20";
  r := Candies(21); expect r == 10, "impl test 16.21";
  r := Candies(22); expect r == 10, "impl test 16.22";
  r := Candies(23); expect r == 11, "impl test 16.23";
  r := Candies(24); expect r == 11, "impl test 16.24";
  r := Candies(25); expect r == 12, "impl test 16.25";
  r := Candies(26); expect r == 12, "impl test 16.26";
  r := Candies(27); expect r == 13, "impl test 16.27";
  r := Candies(28); expect r == 13, "impl test 16.28";
  r := Candies(29); expect r == 14, "impl test 16.29";
  r := Candies(30); expect r == 14, "impl test 16.30";
  r := Candies(31); expect r == 15, "impl test 16.31";

  // Test 17
  r := Candies(54334); expect r == 27166, "impl test 17.1";

  // Test 18
  r := Candies(54332); expect r == 27165, "impl test 18.1";

  // Test 19
  r := Candies(54331); expect r == 27165, "impl test 19.1";

  // Test 20
  r := Candies(54335); expect r == 27167, "impl test 20.1";

  print "All tests passed\n";
}
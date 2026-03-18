method Candies(n: int) returns (ways: int)
{
  if n <= 2 {
    ways := 0;
  } else {
    ways := (n - 1) / 2;
  }
}

method Main()
{
  var r: int;

  // Test 1
  r := Candies(7); expect r == 3;
  r := Candies(1); expect r == 0;
  r := Candies(2); expect r == 0;
  r := Candies(3); expect r == 1;
  r := Candies(2000000000); expect r == 999999999;
  r := Candies(763243547); expect r == 381621773;

  // Test 2
  r := Candies(1); expect r == 0;
  r := Candies(2); expect r == 0;

  // Test 3
  r := Candies(108139); expect r == 54069;

  // Test 4
  r := Candies(1); expect r == 0;
  r := Candies(1); expect r == 0;
  r := Candies(1); expect r == 0;
  r := Candies(1); expect r == 0;
  r := Candies(1); expect r == 0;

  // Test 5
  r := Candies(1); expect r == 0;
  r := Candies(1); expect r == 0;
  r := Candies(1); expect r == 0;
  r := Candies(1); expect r == 0;
  r := Candies(1); expect r == 0;
  r := Candies(1); expect r == 0;
  r := Candies(1); expect r == 0;
  r := Candies(1); expect r == 0;
  r := Candies(1); expect r == 0;
  r := Candies(1); expect r == 0;
  r := Candies(1); expect r == 0;
  r := Candies(1); expect r == 0;
  r := Candies(1); expect r == 0;
  r := Candies(1); expect r == 0;
  r := Candies(1); expect r == 0;
  r := Candies(1); expect r == 0;
  r := Candies(1); expect r == 0;
  r := Candies(1); expect r == 0;
  r := Candies(1); expect r == 0;
  r := Candies(1); expect r == 0;
  r := Candies(1); expect r == 0;
  r := Candies(1); expect r == 0;
  r := Candies(1); expect r == 0;
  r := Candies(1); expect r == 0;
  r := Candies(1); expect r == 0;
  r := Candies(1); expect r == 0;
  r := Candies(1); expect r == 0;
  r := Candies(1); expect r == 0;
  r := Candies(1); expect r == 0;
  r := Candies(1); expect r == 0;
  r := Candies(1); expect r == 0;
  r := Candies(1); expect r == 0;
  r := Candies(1); expect r == 0;
  r := Candies(1); expect r == 0;
  r := Candies(1); expect r == 0;
  r := Candies(1); expect r == 0;
  r := Candies(1); expect r == 0;
  r := Candies(1); expect r == 0;
  r := Candies(1); expect r == 0;

  // Test 6
  r := Candies(121112422); expect r == 60556210;

  // Test 7
  r := Candies(1411); expect r == 705;

  // Test 8
  r := Candies(2); expect r == 0;
  r := Candies(3); expect r == 1;
  r := Candies(5); expect r == 2;
  r := Candies(7); expect r == 3;
  r := Candies(9); expect r == 4;
  r := Candies(8); expect r == 3;
  r := Candies(6); expect r == 2;
  r := Candies(5); expect r == 2;
  r := Candies(4); expect r == 1;
  r := Candies(4); expect r == 1;
  r := Candies(9); expect r == 4;
  r := Candies(4); expect r == 1;
  r := Candies(5); expect r == 2;
  r := Candies(6); expect r == 2;
  r := Candies(8); expect r == 3;
  r := Candies(1); expect r == 0;
  r := Candies(5); expect r == 2;
  r := Candies(4); expect r == 1;
  r := Candies(3); expect r == 1;
  r := Candies(10); expect r == 4;
  r := Candies(7); expect r == 3;
  r := Candies(1); expect r == 0;
  r := Candies(1); expect r == 0;
  r := Candies(4); expect r == 1;
  r := Candies(3); expect r == 1;
  r := Candies(5); expect r == 2;
  r := Candies(6); expect r == 2;
  r := Candies(2); expect r == 0;
  r := Candies(5); expect r == 2;
  r := Candies(9); expect r == 4;
  r := Candies(9); expect r == 4;
  r := Candies(6); expect r == 2;
  r := Candies(6); expect r == 2;
  r := Candies(4); expect r == 1;
  r := Candies(5); expect r == 2;
  r := Candies(3); expect r == 1;
  r := Candies(10); expect r == 4;
  r := Candies(10); expect r == 4;
  r := Candies(1); expect r == 0;

  // Test 9
  r := Candies(7); expect r == 3;
  r := Candies(1); expect r == 0;
  r := Candies(2); expect r == 0;
  r := Candies(3); expect r == 1;
  r := Candies(2000000000); expect r == 999999999;
  r := Candies(763243547); expect r == 381621773;
  r := Candies(7); expect r == 3;
  r := Candies(1); expect r == 0;
  r := Candies(2); expect r == 0;
  r := Candies(3); expect r == 1;
  r := Candies(2000000000); expect r == 999999999;
  r := Candies(763243547); expect r == 381621773;
  r := Candies(7); expect r == 3;
  r := Candies(1); expect r == 0;
  r := Candies(2); expect r == 0;
  r := Candies(3); expect r == 1;
  r := Candies(2000000000); expect r == 999999999;
  r := Candies(763243547); expect r == 381621773;
  r := Candies(7); expect r == 3;
  r := Candies(1); expect r == 0;
  r := Candies(2); expect r == 0;
  r := Candies(3); expect r == 1;
  r := Candies(2000000000); expect r == 999999999;
  r := Candies(763243547); expect r == 381621773;
  r := Candies(7); expect r == 3;
  r := Candies(1); expect r == 0;
  r := Candies(2); expect r == 0;
  r := Candies(3); expect r == 1;
  r := Candies(2000000000); expect r == 999999999;
  r := Candies(763243547); expect r == 381621773;
  r := Candies(7); expect r == 3;
  r := Candies(1); expect r == 0;
  r := Candies(2); expect r == 0;
  r := Candies(3); expect r == 1;
  r := Candies(2000000000); expect r == 999999999;
  r := Candies(763243547); expect r == 381621773;
  r := Candies(7); expect r == 3;
  r := Candies(1); expect r == 0;
  r := Candies(2); expect r == 0;

  // Test 10
  r := Candies(1); expect r == 0;
  r := Candies(2); expect r == 0;
  r := Candies(3); expect r == 1;
  r := Candies(4); expect r == 1;
  r := Candies(5); expect r == 2;
  r := Candies(6); expect r == 2;
  r := Candies(7); expect r == 3;
  r := Candies(8); expect r == 3;
  r := Candies(9); expect r == 4;
  r := Candies(10); expect r == 4;
  r := Candies(11); expect r == 5;
  r := Candies(12); expect r == 5;
  r := Candies(13); expect r == 6;
  r := Candies(14); expect r == 6;
  r := Candies(15); expect r == 7;
  r := Candies(16); expect r == 7;
  r := Candies(17); expect r == 8;
  r := Candies(18); expect r == 8;
  r := Candies(19); expect r == 9;
  r := Candies(20); expect r == 9;
  r := Candies(21); expect r == 10;
  r := Candies(22); expect r == 10;
  r := Candies(23); expect r == 11;
  r := Candies(24); expect r == 11;
  r := Candies(25); expect r == 12;
  r := Candies(26); expect r == 12;
  r := Candies(27); expect r == 13;
  r := Candies(28); expect r == 13;
  r := Candies(29); expect r == 14;
  r := Candies(30); expect r == 14;
  r := Candies(31); expect r == 15;
  r := Candies(32); expect r == 15;
  r := Candies(32); expect r == 15;
  r := Candies(34); expect r == 16;
  r := Candies(35); expect r == 17;
  r := Candies(36); expect r == 17;
  r := Candies(37); expect r == 18;
  r := Candies(35); expect r == 17;
  r := Candies(39); expect r == 19;

  // Test 11
  r := Candies(710); expect r == 354;
  r := Candies(896); expect r == 447;
  r := Candies(635); expect r == 317;
  r := Candies(909); expect r == 454;
  r := Candies(528); expect r == 263;
  r := Candies(799); expect r == 399;
  r := Candies(184); expect r == 91;
  r := Candies(970); expect r == 484;
  r := Candies(731); expect r == 365;
  r := Candies(285); expect r == 142;
  r := Candies(481); expect r == 240;
  r := Candies(62); expect r == 30;
  r := Candies(829); expect r == 414;
  r := Candies(815); expect r == 407;
  r := Candies(204); expect r == 101;
  r := Candies(927); expect r == 463;
  r := Candies(48); expect r == 23;
  r := Candies(958); expect r == 478;
  r := Candies(858); expect r == 428;
  r := Candies(549); expect r == 274;
  r := Candies(722); expect r == 360;
  r := Candies(900); expect r == 449;
  r := Candies(290); expect r == 144;
  r := Candies(96); expect r == 47;
  r := Candies(414); expect r == 206;
  r := Candies(323); expect r == 161;
  r := Candies(488); expect r == 243;
  r := Candies(140); expect r == 69;
  r := Candies(494); expect r == 246;
  r := Candies(286); expect r == 142;
  r := Candies(783); expect r == 391;
  r := Candies(551); expect r == 275;
  r := Candies(896); expect r == 447;
  r := Candies(580); expect r == 289;
  r := Candies(724); expect r == 361;
  r := Candies(766); expect r == 382;
  r := Candies(841); expect r == 420;
  r := Candies(914); expect r == 456;
  r := Candies(200); expect r == 99;
  r := Candies(170); expect r == 84;
  r := Candies(384); expect r == 191;
  r := Candies(664); expect r == 331;
  r := Candies(14); expect r == 6;
  r := Candies(203); expect r == 101;
  r := Candies(582); expect r == 290;
  r := Candies(203); expect r == 101;
  r := Candies(678); expect r == 338;
  r := Candies(502); expect r == 250;
  r := Candies(677); expect r == 338;
  r := Candies(318); expect r == 158;
  r := Candies(189); expect r == 94;
  r := Candies(144); expect r == 71;
  r := Candies(97); expect r == 48;
  r := Candies(330); expect r == 164;
  r := Candies(169); expect r == 84;
  r := Candies(20); expect r == 9;
  r := Candies(492); expect r == 245;
  r := Candies(233); expect r == 116;
  r := Candies(198); expect r == 98;
  r := Candies(876); expect r == 437;
  r := Candies(697); expect r == 348;
  r := Candies(624); expect r == 311;
  r := Candies(877); expect r == 438;
  r := Candies(514); expect r == 256;
  r := Candies(828); expect r == 413;
  r := Candies(41); expect r == 20;
  r := Candies(575); expect r == 287;
  r := Candies(959); expect r == 479;
  r := Candies(499); expect r == 249;
  r := Candies(786); expect r == 392;
  r := Candies(621); expect r == 310;
  r := Candies(878); expect r == 438;
  r := Candies(547); expect r == 273;
  r := Candies(409); expect r == 204;
  r := Candies(194); expect r == 96;
  r := Candies(59); expect r == 29;
  r := Candies(657); expect r == 328;
  r := Candies(893); expect r == 446;
  r := Candies(230); expect r == 114;
  r := Candies(559); expect r == 279;
  r := Candies(170); expect r == 84;
  r := Candies(238); expect r == 118;
  r := Candies(752); expect r == 375;
  r := Candies(854); expect r == 426;
  r := Candies(385); expect r == 192;
  r := Candies(365); expect r == 182;
  r := Candies(415); expect r == 207;
  r := Candies(505); expect r == 252;
  r := Candies(584); expect r == 291;
  r := Candies(434); expect r == 216;
  r := Candies(135); expect r == 67;
  r := Candies(136); expect r == 67;
  r := Candies(610); expect r == 304;
  r := Candies(525); expect r == 262;
  r := Candies(945); expect r == 472;
  r := Candies(889); expect r == 444;
  r := Candies(941); expect r == 470;
  r := Candies(579); expect r == 289;

  // Test 12
  r := Candies(1); expect r == 0;
  r := Candies(1); expect r == 0;
  r := Candies(1); expect r == 0;

  // Test 13
  r := Candies(10); expect r == 4;

  // Test 14
  r := Candies(1); expect r == 0;
  r := Candies(7); expect r == 3;
  r := Candies(1); expect r == 0;
  r := Candies(2); expect r == 0;
  r := Candies(3); expect r == 1;
  r := Candies(2000000000); expect r == 999999999;
  r := Candies(763243547); expect r == 381621773;

  // Test 15
  r := Candies(3); expect r == 1;
  r := Candies(4); expect r == 1;
  r := Candies(5); expect r == 2;

  // Test 16
  r := Candies(1); expect r == 0;
  r := Candies(2); expect r == 0;
  r := Candies(3); expect r == 1;
  r := Candies(4); expect r == 1;
  r := Candies(5); expect r == 2;
  r := Candies(6); expect r == 2;
  r := Candies(7); expect r == 3;
  r := Candies(8); expect r == 3;
  r := Candies(9); expect r == 4;
  r := Candies(10); expect r == 4;
  r := Candies(11); expect r == 5;
  r := Candies(12); expect r == 5;
  r := Candies(13); expect r == 6;
  r := Candies(14); expect r == 6;
  r := Candies(15); expect r == 7;
  r := Candies(16); expect r == 7;
  r := Candies(17); expect r == 8;
  r := Candies(18); expect r == 8;
  r := Candies(19); expect r == 9;
  r := Candies(20); expect r == 9;
  r := Candies(21); expect r == 10;
  r := Candies(22); expect r == 10;
  r := Candies(23); expect r == 11;
  r := Candies(24); expect r == 11;
  r := Candies(25); expect r == 12;
  r := Candies(26); expect r == 12;
  r := Candies(27); expect r == 13;
  r := Candies(28); expect r == 13;
  r := Candies(29); expect r == 14;
  r := Candies(30); expect r == 14;
  r := Candies(31); expect r == 15;

  // Test 17
  r := Candies(54334); expect r == 27166;

  // Test 18
  r := Candies(54332); expect r == 27165;

  // Test 19
  r := Candies(54331); expect r == 27165;

  // Test 20
  r := Candies(54335); expect r == 27167;

  print "All tests passed\n";
}
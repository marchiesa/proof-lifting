function Gcd(a: int, b: int): int
  requires a > 0 && b > 0
  decreases b
{
  if a % b == 0 then b
  else Gcd(b, a % b)
}

predicate SpecEnsures1(n: int, result: int)
  requires n >= 2
{
  exists a: int | 1 <= a && a < n :: exists b: int | a < b && b <= n :: Gcd(a, b) == result
}

predicate SpecEnsures2(n: int, result: int)
  requires n >= 2
{
  forall a: int | 1 <= a && a < n :: forall b: int | a < b && b <= n :: Gcd(a, b) <= result
}

predicate Spec(n: int, result: int)
  requires n >= 2
{
  SpecEnsures1(n, result) && SpecEnsures2(n, result)
}

method MaximumGCD(n: int) returns (result: int)
  requires n >= 2
  ensures exists a: int | 1 <= a && a < n :: exists b: int | a < b && b <= n :: Gcd(a, b) == result
  ensures forall a: int | 1 <= a && a < n :: forall b: int | a < b && b <= n :: Gcd(a, b) <= result
{
  result := n / 2;
}

method Main()
{
  // === SPEC POSITIVE TESTS (small n from positive test pairs) ===
  expect Spec(2, 1), "spec positive 1";
  expect Spec(3, 1), "spec positive 2";
  expect Spec(4, 2), "spec positive 3";
  expect Spec(5, 2), "spec positive 4";
  expect Spec(6, 3), "spec positive 5";
  expect Spec(7, 3), "spec positive 6";

  // === SPEC NEGATIVE TESTS (wrong outputs from negative test pairs, scaled to small n) ===
  expect !Spec(3, 2), "spec negative 1";   // Negative 1: n=3 wrong=2 (correct=1)
  expect !Spec(2, 2), "spec negative 2";   // Negative 2: n=2 wrong=2 (correct=1)
  expect !Spec(2, 0), "spec negative 3";   // wrong value 0 for n=2
  expect !Spec(4, 1), "spec negative 4";   // too low for n=4 (correct=2)
  expect !Spec(4, 3), "spec negative 5";   // too high for n=4 (correct=2)
  expect !Spec(5, 1), "spec negative 6";   // too low for n=5 (correct=2)
  expect !Spec(5, 3), "spec negative 7";   // too high for n=5 (correct=2)

  // === IMPLEMENTATION TESTS (full-size from positive test pairs) ===
  var r2 := MaximumGCD(2);
  expect r2 == 1, "MaximumGCD(2) failed";
  var r3 := MaximumGCD(3);
  expect r3 == 1, "MaximumGCD(3) failed";
  var r4 := MaximumGCD(4);
  expect r4 == 2, "MaximumGCD(4) failed";
  var r5 := MaximumGCD(5);
  expect r5 == 2, "MaximumGCD(5) failed";
  var r6 := MaximumGCD(6);
  expect r6 == 3, "MaximumGCD(6) failed";
  var r7 := MaximumGCD(7);
  expect r7 == 3, "MaximumGCD(7) failed";
  var r8 := MaximumGCD(8);
  expect r8 == 4, "MaximumGCD(8) failed";
  var r9 := MaximumGCD(9);
  expect r9 == 4, "MaximumGCD(9) failed";
  var r10 := MaximumGCD(10);
  expect r10 == 5, "MaximumGCD(10) failed";
  var r11 := MaximumGCD(11);
  expect r11 == 5, "MaximumGCD(11) failed";
  var r12 := MaximumGCD(12);
  expect r12 == 6, "MaximumGCD(12) failed";
  var r13 := MaximumGCD(13);
  expect r13 == 6, "MaximumGCD(13) failed";
  var r14 := MaximumGCD(14);
  expect r14 == 7, "MaximumGCD(14) failed";
  var r15 := MaximumGCD(15);
  expect r15 == 7, "MaximumGCD(15) failed";
  var r16 := MaximumGCD(16);
  expect r16 == 8, "MaximumGCD(16) failed";
  var r17 := MaximumGCD(17);
  expect r17 == 8, "MaximumGCD(17) failed";
  var r18 := MaximumGCD(18);
  expect r18 == 9, "MaximumGCD(18) failed";
  var r19 := MaximumGCD(19);
  expect r19 == 9, "MaximumGCD(19) failed";
  var r20 := MaximumGCD(20);
  expect r20 == 10, "MaximumGCD(20) failed";
  var r21 := MaximumGCD(21);
  expect r21 == 10, "MaximumGCD(21) failed";
  var r22 := MaximumGCD(22);
  expect r22 == 11, "MaximumGCD(22) failed";
  var r23 := MaximumGCD(23);
  expect r23 == 11, "MaximumGCD(23) failed";
  var r24 := MaximumGCD(24);
  expect r24 == 12, "MaximumGCD(24) failed";
  var r25 := MaximumGCD(25);
  expect r25 == 12, "MaximumGCD(25) failed";
  var r26 := MaximumGCD(26);
  expect r26 == 13, "MaximumGCD(26) failed";
  var r27 := MaximumGCD(27);
  expect r27 == 13, "MaximumGCD(27) failed";
  var r28 := MaximumGCD(28);
  expect r28 == 14, "MaximumGCD(28) failed";
  var r29 := MaximumGCD(29);
  expect r29 == 14, "MaximumGCD(29) failed";
  var r30 := MaximumGCD(30);
  expect r30 == 15, "MaximumGCD(30) failed";
  var r31 := MaximumGCD(31);
  expect r31 == 15, "MaximumGCD(31) failed";
  var r32 := MaximumGCD(32);
  expect r32 == 16, "MaximumGCD(32) failed";
  var r33 := MaximumGCD(33);
  expect r33 == 16, "MaximumGCD(33) failed";
  var r34 := MaximumGCD(34);
  expect r34 == 17, "MaximumGCD(34) failed";
  var r35 := MaximumGCD(35);
  expect r35 == 17, "MaximumGCD(35) failed";
  var r36 := MaximumGCD(36);
  expect r36 == 18, "MaximumGCD(36) failed";
  var r37 := MaximumGCD(37);
  expect r37 == 18, "MaximumGCD(37) failed";
  var r38 := MaximumGCD(38);
  expect r38 == 19, "MaximumGCD(38) failed";
  var r39 := MaximumGCD(39);
  expect r39 == 19, "MaximumGCD(39) failed";
  var r40 := MaximumGCD(40);
  expect r40 == 20, "MaximumGCD(40) failed";
  var r41 := MaximumGCD(41);
  expect r41 == 20, "MaximumGCD(41) failed";
  var r42 := MaximumGCD(42);
  expect r42 == 21, "MaximumGCD(42) failed";
  var r43 := MaximumGCD(43);
  expect r43 == 21, "MaximumGCD(43) failed";
  var r44 := MaximumGCD(44);
  expect r44 == 22, "MaximumGCD(44) failed";
  var r45 := MaximumGCD(45);
  expect r45 == 22, "MaximumGCD(45) failed";
  var r46 := MaximumGCD(46);
  expect r46 == 23, "MaximumGCD(46) failed";
  var r47 := MaximumGCD(47);
  expect r47 == 23, "MaximumGCD(47) failed";
  var r48 := MaximumGCD(48);
  expect r48 == 24, "MaximumGCD(48) failed";
  var r49 := MaximumGCD(49);
  expect r49 == 24, "MaximumGCD(49) failed";
  var r50 := MaximumGCD(50);
  expect r50 == 25, "MaximumGCD(50) failed";
  var r51 := MaximumGCD(51);
  expect r51 == 25, "MaximumGCD(51) failed";
  var r52 := MaximumGCD(52);
  expect r52 == 26, "MaximumGCD(52) failed";
  var r53 := MaximumGCD(53);
  expect r53 == 26, "MaximumGCD(53) failed";
  var r54 := MaximumGCD(54);
  expect r54 == 27, "MaximumGCD(54) failed";
  var r55 := MaximumGCD(55);
  expect r55 == 27, "MaximumGCD(55) failed";
  var r56 := MaximumGCD(56);
  expect r56 == 28, "MaximumGCD(56) failed";
  var r57 := MaximumGCD(57);
  expect r57 == 28, "MaximumGCD(57) failed";
  var r58 := MaximumGCD(58);
  expect r58 == 29, "MaximumGCD(58) failed";
  var r59 := MaximumGCD(59);
  expect r59 == 29, "MaximumGCD(59) failed";
  var r60 := MaximumGCD(60);
  expect r60 == 30, "MaximumGCD(60) failed";
  var r61 := MaximumGCD(61);
  expect r61 == 30, "MaximumGCD(61) failed";
  var r62 := MaximumGCD(62);
  expect r62 == 31, "MaximumGCD(62) failed";
  var r63 := MaximumGCD(63);
  expect r63 == 31, "MaximumGCD(63) failed";
  var r64 := MaximumGCD(64);
  expect r64 == 32, "MaximumGCD(64) failed";
  var r65 := MaximumGCD(65);
  expect r65 == 32, "MaximumGCD(65) failed";
  var r66 := MaximumGCD(66);
  expect r66 == 33, "MaximumGCD(66) failed";
  var r67 := MaximumGCD(67);
  expect r67 == 33, "MaximumGCD(67) failed";
  var r68 := MaximumGCD(68);
  expect r68 == 34, "MaximumGCD(68) failed";
  var r69 := MaximumGCD(69);
  expect r69 == 34, "MaximumGCD(69) failed";
  var r70 := MaximumGCD(70);
  expect r70 == 35, "MaximumGCD(70) failed";
  var r71 := MaximumGCD(71);
  expect r71 == 35, "MaximumGCD(71) failed";
  var r72 := MaximumGCD(72);
  expect r72 == 36, "MaximumGCD(72) failed";
  var r73 := MaximumGCD(73);
  expect r73 == 36, "MaximumGCD(73) failed";
  var r74 := MaximumGCD(74);
  expect r74 == 37, "MaximumGCD(74) failed";
  var r75 := MaximumGCD(75);
  expect r75 == 37, "MaximumGCD(75) failed";
  var r76 := MaximumGCD(76);
  expect r76 == 38, "MaximumGCD(76) failed";
  var r77 := MaximumGCD(77);
  expect r77 == 38, "MaximumGCD(77) failed";
  var r78 := MaximumGCD(78);
  expect r78 == 39, "MaximumGCD(78) failed";
  var r79 := MaximumGCD(79);
  expect r79 == 39, "MaximumGCD(79) failed";
  var r80 := MaximumGCD(80);
  expect r80 == 40, "MaximumGCD(80) failed";
  var r81 := MaximumGCD(81);
  expect r81 == 40, "MaximumGCD(81) failed";
  var r82 := MaximumGCD(82);
  expect r82 == 41, "MaximumGCD(82) failed";
  var r83 := MaximumGCD(83);
  expect r83 == 41, "MaximumGCD(83) failed";
  var r84 := MaximumGCD(84);
  expect r84 == 42, "MaximumGCD(84) failed";
  var r85 := MaximumGCD(85);
  expect r85 == 42, "MaximumGCD(85) failed";
  var r86 := MaximumGCD(86);
  expect r86 == 43, "MaximumGCD(86) failed";
  var r87 := MaximumGCD(87);
  expect r87 == 43, "MaximumGCD(87) failed";
  var r88 := MaximumGCD(88);
  expect r88 == 44, "MaximumGCD(88) failed";
  var r89 := MaximumGCD(89);
  expect r89 == 44, "MaximumGCD(89) failed";
  var r90 := MaximumGCD(90);
  expect r90 == 45, "MaximumGCD(90) failed";
  var r91 := MaximumGCD(91);
  expect r91 == 45, "MaximumGCD(91) failed";
  var r92 := MaximumGCD(92);
  expect r92 == 46, "MaximumGCD(92) failed";
  var r93 := MaximumGCD(93);
  expect r93 == 46, "MaximumGCD(93) failed";
  var r94 := MaximumGCD(94);
  expect r94 == 47, "MaximumGCD(94) failed";
  var r95 := MaximumGCD(95);
  expect r95 == 47, "MaximumGCD(95) failed";
  var r96 := MaximumGCD(96);
  expect r96 == 48, "MaximumGCD(96) failed";
  var r97 := MaximumGCD(97);
  expect r97 == 48, "MaximumGCD(97) failed";
  var r98 := MaximumGCD(98);
  expect r98 == 49, "MaximumGCD(98) failed";
  var r99 := MaximumGCD(99);
  expect r99 == 49, "MaximumGCD(99) failed";
  var r100 := MaximumGCD(100);
  expect r100 == 50, "MaximumGCD(100) failed";
  var r101 := MaximumGCD(101);
  expect r101 == 50, "MaximumGCD(101) failed";

  print "All tests passed\n";
}
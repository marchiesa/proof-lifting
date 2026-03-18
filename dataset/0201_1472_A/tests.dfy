function MaxPieces(w: int, h: int): int
  requires w > 0 && h > 0
  decreases w + h
{
  if w % 2 == 0 && h % 2 == 0 then
    var viaW := 2 * MaxPieces(w / 2, h);
    var viaH := 2 * MaxPieces(w, h / 2);
    if viaW >= viaH then viaW else viaH
  else if w % 2 == 0 then
    2 * MaxPieces(w / 2, h)
  else if h % 2 == 0 then
    2 * MaxPieces(w, h / 2)
  else
    1
}

method CardsForFriends(w: int, h: int, n: int) returns (result: bool)
  requires w > 0 && h > 0
  ensures result == (MaxPieces(w, h) >= n)
{
  var cnt := 1;
  var ww := w;
  var hh := h;
  while ww > 0 && ww % 2 == 0
  {
    cnt := cnt * 2;
    ww := ww / 2;
  }
  while hh > 0 && hh % 2 == 0
  {
    cnt := cnt * 2;
    hh := hh / 2;
  }
  result := cnt >= n;
}

method Main()
{
  // ===== SPEC POSITIVE TESTS =====
  // Top-level ensures predicate: result == (MaxPieces(w, h) >= n)
  // Using small inputs to avoid expensive branching recursion

  expect (MaxPieces(2, 2) >= 3) == true,  "spec positive 1";  // Test 1.1: (2,2,3)->true
  expect (MaxPieces(3, 3) >= 2) == false,  "spec positive 2";  // Test 1.2: (3,3,2)->false
  expect (MaxPieces(5, 2) >= 2) == true,  "spec positive 3";  // Test 1.3 scaled: (5,10,2)->true
  expect (MaxPieces(1, 1) >= 1) == true,  "spec positive 4";  // Test 6.5: (1,1,1)->true
  expect (MaxPieces(3, 3) >= 1) == true,  "spec positive 5";  // Test 6.6 scaled: (13,13,1)->true
  expect (MaxPieces(1, 4) >= 4) == true,  "spec positive 6";  // Test 1.5: (1,4,4)->true
  expect (MaxPieces(2, 1) >= 2) == true,  "spec positive 7";  // Test 6.13 scaled: (150,15,2)->true

  // ===== SPEC NEGATIVE TESTS =====
  // Same predicate with WRONG outputs — spec must reject these

  expect !((MaxPieces(2, 2) >= 3) == false),  "spec negative 1";  // Neg1: correct=true, wrong=false
  expect !((MaxPieces(2, 2) >= 4) == false),  "spec negative 2";  // Neg2 scaled: correct=true, wrong=false
  expect !((MaxPieces(4, 1) >= 3) == false),  "spec negative 3";  // Neg3 scaled: correct=true, wrong=false
  expect !((MaxPieces(3, 1) >= 2) == true),   "spec negative 4";  // Neg4 repr: correct=false, wrong=true
  expect !((MaxPieces(2, 1) >= 2) == false),  "spec negative 5";  // Neg5 scaled: correct=true, wrong=false
  expect !((MaxPieces(3, 3) >= 1) == false),  "spec negative 6";  // Neg6 repr: correct=true, wrong=false
  expect !((MaxPieces(1, 1) >= 2) == true),   "spec negative 7";  // Neg7 scaled: correct=false, wrong=true

  // ===== IMPLEMENTATION TESTS =====
  var r: bool;

  // Test 1
  r := CardsForFriends(2, 2, 3);
  expect r == true, "impl test 1.1: (2,2,3) expected true";
  r := CardsForFriends(3, 3, 2);
  expect r == false, "impl test 1.2: (3,3,2) expected false";
  r := CardsForFriends(5, 10, 2);
  expect r == true, "impl test 1.3: (5,10,2) expected true";
  r := CardsForFriends(11, 13, 1);
  expect r == true, "impl test 1.4: (11,13,1) expected true";
  r := CardsForFriends(1, 4, 4);
  expect r == true, "impl test 1.5: (1,4,4) expected true";

  // Test 2
  r := CardsForFriends(8192, 8192, 67108864);
  expect r == true, "impl test 2.1";

  // Test 3
  r := CardsForFriends(1024, 1024, 22212);
  expect r == true, "impl test 3.1";

  // Test 4
  r := CardsForFriends(6144, 8192, 16777216);
  expect r == true, "impl test 4.1";
  r := CardsForFriends(8192, 6144, 16777216);
  expect r == true, "impl test 4.2";
  r := CardsForFriends(8192, 8192, 67108864);
  expect r == true, "impl test 4.3";
  r := CardsForFriends(8192, 8192, 67108865);
  expect r == false, "impl test 4.4";
  r := CardsForFriends(6144, 8192, 67108864);
  expect r == false, "impl test 4.5";
  r := CardsForFriends(8192, 6044, 67108864);
  expect r == false, "impl test 4.6";
  r := CardsForFriends(6144, 8192, 16777217);
  expect r == false, "impl test 4.7";
  r := CardsForFriends(8192, 6044, 16777217);
  expect r == false, "impl test 4.8";

  // Test 5
  r := CardsForFriends(8192, 8192, 1000000);
  expect r == true, "impl test 5.1";

  // Test 6
  r := CardsForFriends(8192, 8192, 67108864);
  expect r == true, "impl test 6.1";
  r := CardsForFriends(8192, 8192, 67108865);
  expect r == false, "impl test 6.2";
  r := CardsForFriends(8192, 8192, 70000000);
  expect r == false, "impl test 6.3";
  r := CardsForFriends(8192, 8192, 67108863);
  expect r == true, "impl test 6.4";
  r := CardsForFriends(1, 1, 1);
  expect r == true, "impl test 6.5";
  r := CardsForFriends(13, 13, 1);
  expect r == true, "impl test 6.6";
  r := CardsForFriends(1000, 1000, 100);
  expect r == false, "impl test 6.7";
  r := CardsForFriends(100, 15, 16);
  expect r == false, "impl test 6.8";
  r := CardsForFriends(157, 185, 95);
  expect r == false, "impl test 6.9";
  r := CardsForFriends(1257, 1895, 12);
  expect r == false, "impl test 6.10";
  r := CardsForFriends(1574, 4984, 164);
  expect r == false, "impl test 6.11";
  r := CardsForFriends(1564, 8917, 15);
  expect r == false, "impl test 6.12";
  r := CardsForFriends(150, 15, 2);
  expect r == true, "impl test 6.13";
  r := CardsForFriends(1500, 10, 40);
  expect r == false, "impl test 6.14";
  r := CardsForFriends(1, 10000, 1000);
  expect r == false, "impl test 6.15";
  r := CardsForFriends(1, 10000, 10000);
  expect r == false, "impl test 6.16";

  // Test 7
  r := CardsForFriends(8192, 8192, 67108865);
  expect r == false, "impl test 7.1";

  print "All tests passed\n";
}
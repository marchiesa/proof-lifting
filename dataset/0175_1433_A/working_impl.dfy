method BoringApartments(x: int) returns (keypresses: int)
{
  var ans := 0;
  var ok := 0;
  var i := 1;
  while i <= 9 {
    var n := 0;
    var j := 0;
    while j < 4 {
      n := n * 10 + i;
      ans := ans + (j + 1);
      if n == x {
        ok := 1;
        break;
      }
      j := j + 1;
    }
    if ok == 1 {
      break;
    }
    i := i + 1;
  }
  return ans;
}

method Main()
{
  var r: int;

  // Test 1
  r := BoringApartments(22);
  expect r == 13, "Test 1: x=22";
  r := BoringApartments(9999);
  expect r == 90, "Test 1: x=9999";
  r := BoringApartments(1);
  expect r == 1, "Test 1: x=1";
  r := BoringApartments(777);
  expect r == 66, "Test 1: x=777";

  // Test 2
  r := BoringApartments(1);
  expect r == 1, "Test 2: x=1";
  r := BoringApartments(2);
  expect r == 11, "Test 2: x=2";
  r := BoringApartments(3);
  expect r == 21, "Test 2: x=3";
  r := BoringApartments(4);
  expect r == 31, "Test 2: x=4";
  r := BoringApartments(5);
  expect r == 41, "Test 2: x=5";
  r := BoringApartments(6);
  expect r == 51, "Test 2: x=6";
  r := BoringApartments(7);
  expect r == 61, "Test 2: x=7";
  r := BoringApartments(8);
  expect r == 71, "Test 2: x=8";
  r := BoringApartments(9);
  expect r == 81, "Test 2: x=9";
  r := BoringApartments(11);
  expect r == 3, "Test 2: x=11";
  r := BoringApartments(22);
  expect r == 13, "Test 2: x=22";
  r := BoringApartments(33);
  expect r == 23, "Test 2: x=33";
  r := BoringApartments(44);
  expect r == 33, "Test 2: x=44";
  r := BoringApartments(55);
  expect r == 43, "Test 2: x=55";
  r := BoringApartments(66);
  expect r == 53, "Test 2: x=66";
  r := BoringApartments(77);
  expect r == 63, "Test 2: x=77";
  r := BoringApartments(88);
  expect r == 73, "Test 2: x=88";
  r := BoringApartments(99);
  expect r == 83, "Test 2: x=99";
  r := BoringApartments(111);
  expect r == 6, "Test 2: x=111";
  r := BoringApartments(222);
  expect r == 16, "Test 2: x=222";
  r := BoringApartments(333);
  expect r == 26, "Test 2: x=333";
  r := BoringApartments(444);
  expect r == 36, "Test 2: x=444";
  r := BoringApartments(555);
  expect r == 46, "Test 2: x=555";
  r := BoringApartments(666);
  expect r == 56, "Test 2: x=666";
  r := BoringApartments(777);
  expect r == 66, "Test 2: x=777";
  r := BoringApartments(888);
  expect r == 76, "Test 2: x=888";
  r := BoringApartments(999);
  expect r == 86, "Test 2: x=999";
  r := BoringApartments(1111);
  expect r == 10, "Test 2: x=1111";
  r := BoringApartments(2222);
  expect r == 20, "Test 2: x=2222";
  r := BoringApartments(3333);
  expect r == 30, "Test 2: x=3333";
  r := BoringApartments(4444);
  expect r == 40, "Test 2: x=4444";
  r := BoringApartments(5555);
  expect r == 50, "Test 2: x=5555";
  r := BoringApartments(6666);
  expect r == 60, "Test 2: x=6666";
  r := BoringApartments(7777);
  expect r == 70, "Test 2: x=7777";
  r := BoringApartments(8888);
  expect r == 80, "Test 2: x=8888";
  r := BoringApartments(9999);
  expect r == 90, "Test 2: x=9999";

  // Test 3: 36 calls with x=9999, all expecting 90
  var i := 0;
  while i < 36 {
    r := BoringApartments(9999);
    expect r == 90, "Test 3: x=9999";
    i := i + 1;
  }

  // Test 4
  r := BoringApartments(999);
  expect r == 86, "Test 4: x=999";
  r := BoringApartments(33);
  expect r == 23, "Test 4: x=33";
  r := BoringApartments(2222);
  expect r == 20, "Test 4: x=2222";
  r := BoringApartments(22);
  expect r == 13, "Test 4: x=22";
  r := BoringApartments(2222);
  expect r == 20, "Test 4: x=2222 (2)";
  r := BoringApartments(333);
  expect r == 26, "Test 4: x=333";
  r := BoringApartments(4);
  expect r == 31, "Test 4: x=4";
  r := BoringApartments(99);
  expect r == 83, "Test 4: x=99";
  r := BoringApartments(11);
  expect r == 3, "Test 4: x=11";
  r := BoringApartments(444);
  expect r == 36, "Test 4: x=444";
  r := BoringApartments(8888);
  expect r == 80, "Test 4: x=8888";
  r := BoringApartments(444);
  expect r == 36, "Test 4: x=444 (2)";
  r := BoringApartments(2222);
  expect r == 20, "Test 4: x=2222 (3)";
  r := BoringApartments(6666);
  expect r == 60, "Test 4: x=6666";
  r := BoringApartments(666);
  expect r == 56, "Test 4: x=666";
  r := BoringApartments(7);
  expect r == 61, "Test 4: x=7";
  r := BoringApartments(555);
  expect r == 46, "Test 4: x=555";
  r := BoringApartments(5);
  expect r == 41, "Test 4: x=5";
  r := BoringApartments(8);
  expect r == 71, "Test 4: x=8";
  r := BoringApartments(9999);
  expect r == 90, "Test 4: x=9999";

  // Test 5
  r := BoringApartments(22);
  expect r == 13, "Test 5: x=22";

  // Test 6
  r := BoringApartments(1);
  expect r == 1, "Test 6: x=1";

  // Test 7
  r := BoringApartments(9999);
  expect r == 90, "Test 7: x=9999";

  // Test 8
  r := BoringApartments(777);
  expect r == 66, "Test 8: x=777";

  // Test 9
  r := BoringApartments(5);
  expect r == 41, "Test 9: x=5";

  // Test 10
  r := BoringApartments(33);
  expect r == 23, "Test 10: x=33";

  // Test 11
  r := BoringApartments(444);
  expect r == 36, "Test 11: x=444";

  // Test 12
  r := BoringApartments(1111);
  expect r == 10, "Test 12: x=1111";

  // Test 13
  r := BoringApartments(88);
  expect r == 73, "Test 13: x=88";

  // Test 14
  r := BoringApartments(6);
  expect r == 51, "Test 14: x=6";
  r := BoringApartments(222);
  expect r == 16, "Test 14: x=222";
  r := BoringApartments(55);
  expect r == 43, "Test 14: x=55";

  print "All tests passed\n";
}
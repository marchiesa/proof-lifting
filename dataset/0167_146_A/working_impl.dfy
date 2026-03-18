method LuckyTicket(n: int, s: seq<char>) returns (result: bool)
{
  var a := 0;
  var b := 0;
  var half := |s| / 2;
  var i := 0;
  while i < |s|
  {
    if s[i] != '4' && s[i] != '7' {
      result := false;
      return;
    }
    var digit := (s[i] as int) - ('0' as int);
    if i < half {
      a := a + digit;
    } else {
      b := b + digit;
    }
    i := i + 1;
  }
  result := (a == b);
}

method Main()
{
  var r: bool;

  // Test 1
  r := LuckyTicket(2, "47");
  expect r == false, "Test 1 failed";

  // Test 2
  r := LuckyTicket(4, "4738");
  expect r == false, "Test 2 failed";

  // Test 3
  r := LuckyTicket(4, "4774");
  expect r == true, "Test 3 failed";

  // Test 4
  r := LuckyTicket(4, "4570");
  expect r == false, "Test 4 failed";

  // Test 5
  r := LuckyTicket(6, "477477");
  expect r == true, "Test 5 failed";

  // Test 6
  r := LuckyTicket(6, "777777");
  expect r == true, "Test 6 failed";

  // Test 7
  r := LuckyTicket(20, "44444444444444444444");
  expect r == true, "Test 7 failed";

  // Test 8
  r := LuckyTicket(2, "44");
  expect r == true, "Test 8 failed";

  // Test 9
  r := LuckyTicket(10, "4745474547");
  expect r == false, "Test 9 failed";

  // Test 10
  r := LuckyTicket(14, "77770004444444");
  expect r == false, "Test 10 failed";

  // Test 11
  r := LuckyTicket(10, "4747777744");
  expect r == true, "Test 11 failed";

  // Test 12
  r := LuckyTicket(10, "1234567890");
  expect r == false, "Test 12 failed";

  // Test 13
  r := LuckyTicket(50, "44444444444444444444444444444444444444444444444444");
  expect r == true, "Test 13 failed";

  // Test 14
  r := LuckyTicket(50, "44444444444444444444444444444444444444444444444447");
  expect r == false, "Test 14 failed";

  // Test 15
  r := LuckyTicket(50, "74444444444444444444444444444444444444444444444444");
  expect r == false, "Test 15 failed";

  // Test 16
  r := LuckyTicket(50, "07777777777777777777777777777777777777777777777770");
  expect r == false, "Test 16 failed";

  // Test 17
  r := LuckyTicket(50, "77777777777777777777777777777777777777777777777777");
  expect r == true, "Test 17 failed";

  // Test 18
  r := LuckyTicket(50, "44747747774474747747747447777447774747447477444474");
  expect r == true, "Test 18 failed";

  // Test 19
  r := LuckyTicket(48, "447474444777444474747747744774447444747474774474");
  expect r == true, "Test 19 failed";

  // Test 20
  r := LuckyTicket(32, "74474474777444474444747774474774");
  expect r == true, "Test 20 failed";

  print "All tests passed\n";
}
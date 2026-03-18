method Hotelier(events: seq<char>) returns (rooms: seq<int>)
{
  rooms := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
  var idx := 0;
  while idx < |events|
  {
    var ch := events[idx];
    if ch == 'L' {
      var i := 0;
      while i < 10
      {
        if rooms[i] == 0 {
          rooms := rooms[i := 1];
          break;
        }
        i := i + 1;
      }
    } else if ch == 'R' {
      var i := 9;
      while i >= 0
      {
        if rooms[i] == 0 {
          rooms := rooms[i := 1];
          break;
        }
        i := i - 1;
      }
    } else if '0' <= ch <= '9' {
      var i := (ch as int) - ('0' as int);
      rooms := rooms[i := 0];
    }
    idx := idx + 1;
  }
}

method Main()
{
  // Test 1
  var r1 := Hotelier("LLRL1RL1");
  expect r1 == [1,0,1,0,0,0,0,0,1,1], "Test 1 failed";

  // Test 2
  var r2 := Hotelier("L0L0LLRR9");
  expect r2 == [1,1,0,0,0,0,0,0,1,0], "Test 2 failed";

  // Test 3
  var r3 := Hotelier("L");
  expect r3 == [1,0,0,0,0,0,0,0,0,0], "Test 3 failed";

  // Test 4
  var r4 := Hotelier("L0L0R9R9R9R9R9L0R9R9R9R9L0L0L0L0R9L0R9L0R9L0R9R9R9L0L0L0L0L0L0R9L0R9L0R9L0R9L0R9L0L0R9L0R9L0L0L0LR09");
  expect r4 == [0,0,0,0,0,0,0,0,0,0], "Test 4 failed";

  // Test 5
  var r5 := Hotelier("RRLRRLRRLR2L0R6R2L1L3R4L0L6L2L2R5R6R1R3L6R6R8L6L4L3L6R9L6L9L8L7R7L8R1R1R7R7L2L8L2L1R8R2R8L76RR9R4R3R");
  expect r5 == [1,1,1,1,1,1,1,1,1,1], "Test 5 failed";

  // Test 6
  var r6 := Hotelier("RRLLLLLLRR1R7R3L2R0L52RR2R4L1L7L6R4R0R4L5L4L5R2R8L7R0R6R4R8L6L8L4R5R7R3L9R7L64RR8L0R6R4R9L0R9R7R7R0L");
  expect r6 == [1,1,1,1,1,1,1,1,1,1], "Test 6 failed";

  // Test 7
  var r7 := Hotelier("L0L0R9R9R9R9R9L0R9R9R9R9L0L0L0L0R9L0R9L0R9L0R9R9R9L0L0L0L0L0L0R9L0R9L0R9L0R9L0R9L0L0R9L0R9L0L0L0LR09");
  expect r7 == [0,0,0,0,0,0,0,0,0,0], "Test 7 failed";

  // Test 8
  var r8 := Hotelier("LLL210L0L0L0L0LL0L1LLLLLLL34LLL3056LLL5804L7LL5L0L");
  expect r8 == [1,1,1,1,1,1,0,0,0,0], "Test 8 failed";

  // Test 9
  var r9 := Hotelier("LLLLLLLLLL0L2L48LL6L7L7L0L3L0L63LL3L4L9L2L7L6L3L8L2L5L9L0L3L3L9L3L3L3L5L2L2L2L1L8L5L7L9L2L05L0LL6L2L");
  expect r9 == [1,1,1,1,1,1,1,1,1,1], "Test 9 failed";

  // Test 10
  var r10 := Hotelier("LR");
  expect r10 == [1,0,0,0,0,0,0,0,0,1], "Test 10 failed";

  // Test 11
  var r11 := Hotelier("RRR");
  expect r11 == [0,0,0,0,0,0,0,1,1,1], "Test 11 failed";

  // Test 12
  var r12 := Hotelier("RRRL");
  expect r12 == [1,0,0,0,0,0,0,1,1,1], "Test 12 failed";

  // Test 13
  var r13 := Hotelier("LRLLL");
  expect r13 == [1,1,1,1,0,0,0,0,0,1], "Test 13 failed";

  // Test 14
  var r14 := Hotelier("LRRRRR");
  expect r14 == [1,0,0,0,0,1,1,1,1,1], "Test 14 failed";

  // Test 15
  var r15 := Hotelier("LRLLRLL");
  expect r15 == [1,1,1,1,1,0,0,0,1,1], "Test 15 failed";

  // Test 16
  var r16 := Hotelier("RRLRLLRL");
  expect r16 == [1,1,1,1,0,0,1,1,1,1], "Test 16 failed";

  // Test 17
  var r17 := Hotelier("RRRLLLRRR");
  expect r17 == [1,1,1,0,1,1,1,1,1,1], "Test 17 failed";

  // Test 18
  var r18 := Hotelier("LRRLRRLRRL");
  expect r18 == [1,1,1,1,1,1,1,1,1,1], "Test 18 failed";

  // Test 19
  var r19 := Hotelier("LLLLLLLLLL");
  expect r19 == [1,1,1,1,1,1,1,1,1,1], "Test 19 failed";

  // Test 20
  var r20 := Hotelier("LLLLLLL");
  expect r20 == [1,1,1,1,1,1,1,0,0,0], "Test 20 failed";

  print "All tests passed\n";
}
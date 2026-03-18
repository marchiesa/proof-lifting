// --- Specification ---

function LeftmostEmpty(rooms: seq<int>): int
  ensures LeftmostEmpty(rooms) == -1 || (0 <= LeftmostEmpty(rooms) < |rooms|)
  decreases |rooms|
{
  if |rooms| == 0 then -1
  else if rooms[0] == 0 then 0
  else
    var rest := LeftmostEmpty(rooms[1..]);
    if rest == -1 then -1 else rest + 1
}

function RightmostEmpty(rooms: seq<int>): int
  ensures RightmostEmpty(rooms) == -1 || (0 <= RightmostEmpty(rooms) < |rooms|)
  decreases |rooms|
{
  if |rooms| == 0 then -1
  else if rooms[|rooms| - 1] == 0 then |rooms| - 1
  else RightmostEmpty(rooms[..|rooms| - 1])
}

function HotelAfterEvent(rooms: seq<int>, event: char): seq<int>
  requires |rooms| == 10
  ensures |HotelAfterEvent(rooms, event)| == 10
{
  if event == 'L' then
    var i := LeftmostEmpty(rooms);
    if i == -1 then rooms else rooms[i := 1]
  else if event == 'R' then
    var i := RightmostEmpty(rooms);
    if i == -1 then rooms else rooms[i := 1]
  else if '0' <= event <= '9' then
    rooms[(event as int) - ('0' as int) := 0]
  else
    rooms
}

function HotelAfterEvents(events: seq<char>): seq<int>
  ensures |HotelAfterEvents(events)| == 10
  decreases |events|
{
  if |events| == 0 then
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  else
    HotelAfterEvent(HotelAfterEvents(events[..|events| - 1]), events[|events| - 1])
}

// --- Implementation ---

method Hotelier(events: seq<char>) returns (rooms: seq<int>)
  ensures |rooms| == 10
  ensures rooms == HotelAfterEvents(events)
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
  // ==================== SPEC POSITIVE TESTS ====================
  // Top-level ensures: rooms == HotelAfterEvents(events)
  // Testing that HotelAfterEvents produces the correct output.

  // Spec positive 1 (Test 3: 1 event)
  expect HotelAfterEvents("L") == [1,0,0,0,0,0,0,0,0,0], "spec positive 1";

  // Spec positive 2 (Test 10: 2 events)
  expect HotelAfterEvents("LR") == [1,0,0,0,0,0,0,0,0,1], "spec positive 2";

  // Spec positive 3 (Test 1: 8 events)
  expect HotelAfterEvents("LLRL1RL1") == [1,0,1,0,0,0,0,0,1,1], "spec positive 3";

  // Spec positive 4 (Test 2: 9 events)
  expect HotelAfterEvents("L0L0LLRR9") == [1,1,0,0,0,0,0,0,1,0], "spec positive 4";

  // Spec positive 5 (from Main extra tests: 3 events)
  expect HotelAfterEvents("RRR") == [0,0,0,0,0,0,0,1,1,1], "spec positive 5";

  // Spec positive 6 (from Main extra tests: 4 events)
  expect HotelAfterEvents("RRRL") == [1,0,0,0,0,0,0,1,1,1], "spec positive 6";

  // Spec positive 7 (from Main extra tests: 5 events)
  expect HotelAfterEvents("LRLLL") == [1,1,1,1,0,0,0,0,0,1], "spec positive 7";

  // Spec positive 8 (from Main extra tests: 6 events)
  expect HotelAfterEvents("LRRRRR") == [1,0,0,0,0,1,1,1,1,1], "spec positive 8";

  // Spec positive 9 (from Main extra tests: 7 events)
  expect HotelAfterEvents("LRLLRLL") == [1,1,1,1,1,0,0,0,1,1], "spec positive 9";

  // Spec positive 10 (from Main extra tests: 7 events)
  expect HotelAfterEvents("LLLLLLL") == [1,1,1,1,1,1,1,0,0,0], "spec positive 10";

  // ==================== SPEC NEGATIVE TESTS ====================
  // Testing that HotelAfterEvents does NOT produce the wrong output.

  // Spec negative 1 (Neg 3: input "L", wrong "1000000001")
  expect HotelAfterEvents("L") != [1,0,0,0,0,0,0,0,0,1], "spec negative 1";

  // Spec negative 2 (Neg 10: input "LR", wrong "1000000002")
  expect HotelAfterEvents("LR") != [1,0,0,0,0,0,0,0,0,2], "spec negative 2";

  // Spec negative 3 (Neg 1: input "LLRL1RL1", wrong "1010000012")
  expect HotelAfterEvents("LLRL1RL1") != [1,0,1,0,0,0,0,0,1,2], "spec negative 3";

  // Spec negative 4 (Neg 2: input "L0L0LLRR9", wrong "1100000011")
  expect HotelAfterEvents("L0L0LLRR9") != [1,1,0,0,0,0,0,0,1,1], "spec negative 4";

  // Spec negative 5 (Neg 8: input 50 events, wrong "1111110001")
  expect HotelAfterEvents("LLL210L0L0L0L0LL0L1LLLLLLL34LLL3056LLL5804L7LL5L0L") != [1,1,1,1,1,1,0,0,0,1], "spec negative 5";

  // Spec negative 6 (scaled: "RRR" should not be all zeros)
  expect HotelAfterEvents("RRR") != [0,0,0,0,0,0,0,0,0,0], "spec negative 6";

  // Spec negative 7 (scaled: "RRRL" wrong last room)
  expect HotelAfterEvents("RRRL") != [0,0,0,0,0,0,0,1,1,1], "spec negative 7";

  // Spec negative 8 (scaled: "LRLLL" wrong arrangement)
  expect HotelAfterEvents("LRLLL") != [1,1,1,1,0,0,0,0,1,0], "spec negative 8";

  // Spec negative 9 (scaled: "LRRRRR" wrong)
  expect HotelAfterEvents("LRRRRR") != [1,0,0,0,0,1,1,1,1,0], "spec negative 9";

  // Spec negative 10 (scaled: "LLLLLLL" wrong)
  expect HotelAfterEvents("LLLLLLL") != [1,1,1,1,1,1,1,1,0,0], "spec negative 10";

  // ==================== IMPLEMENTATION TESTS ====================
  // Testing: Hotelier returns the correct output for all test pairs.

  // Impl test 1
  var r1 := Hotelier("LLRL1RL1");
  expect r1 == [1,0,1,0,0,0,0,0,1,1], "impl test 1 failed";

  // Impl test 2
  var r2 := Hotelier("L0L0LLRR9");
  expect r2 == [1,1,0,0,0,0,0,0,1,0], "impl test 2 failed";

  // Impl test 3
  var r3 := Hotelier("L");
  expect r3 == [1,0,0,0,0,0,0,0,0,0], "impl test 3 failed";

  // Impl test 4
  var r4 := Hotelier("R9L0L0R9R9L0R9R9L0R9R9R9L0R9R9R9L0L0R9L0R9L0L0L0R9R9L0R9L0R9R9L0R9R9L0R9L0L0R9R9R9L0L0L0L0R9L0L0L0L0");
  expect r4 == [0,0,0,0,0,0,0,0,0,0], "impl test 4 failed";

  // Impl test 5
  var r5 := Hotelier("RRLRRLRRLR2L0R6R2L1L3R4L0L6L2L2R5R6R1R3L6R6R8L6L4L3L6R9L6L9L8L7R7L8R1R1R7R7L2L8L2L1R8R2R8L76RR9R4R3R");
  expect r5 == [1,1,1,1,1,1,1,1,1,1], "impl test 5 failed";

  // Impl test 6
  var r6 := Hotelier("RRLLLLLLRR1R7R3L2R0L52RR2R4L1L7L6R4R0R4L5L4L5R2R8L7R0R6R4R8L6L8L4R5R7R3L9R7L64RR8L0R6R4R9L0R9R7R7R0L");
  expect r6 == [1,1,1,1,1,1,1,1,1,1], "impl test 6 failed";

  // Impl test 7
  var r7 := Hotelier("L0L0R9R9R9R9R9L0R9R9R9R9L0L0L0L0R9L0R9L0R9L0R9R9R9L0L0L0L0L0L0R9L0R9L0R9L0R9L0R9L0L0R9L0R9L0L0L0LR09");
  expect r7 == [0,0,0,0,0,0,0,0,0,0], "impl test 7 failed";

  // Impl test 8
  var r8 := Hotelier("LLL210L0L0L0L0LL0L1LLLLLLL34LLL3056LLL5804L7LL5L0L");
  expect r8 == [1,1,1,1,1,1,0,0,0,0], "impl test 8 failed";

  // Impl test 9
  var r9 := Hotelier("LLLLLLLLLL0L2L48LL6L7L7L0L3L0L63LL3L4L9L2L7L6L3L8L2L5L9L0L3L3L9L3L3L3L5L2L2L2L1L8L5L7L9L2L05L0LL6L2L");
  expect r9 == [1,1,1,1,1,1,1,1,1,1], "impl test 9 failed";

  // Impl test 10
  var r10 := Hotelier("LR");
  expect r10 == [1,0,0,0,0,0,0,0,0,1], "impl test 10 failed";

  // Additional impl tests from original Main
  var r11 := Hotelier("RRR");
  expect r11 == [0,0,0,0,0,0,0,1,1,1], "impl test 11 failed";

  var r12 := Hotelier("RRRL");
  expect r12 == [1,0,0,0,0,0,0,1,1,1], "impl test 12 failed";

  var r13 := Hotelier("LRLLL");
  expect r13 == [1,1,1,1,0,0,0,0,0,1], "impl test 13 failed";

  var r14 := Hotelier("LRRRRR");
  expect r14 == [1,0,0,0,0,1,1,1,1,1], "impl test 14 failed";

  var r15 := Hotelier("LRLLRLL");
  expect r15 == [1,1,1,1,1,0,0,0,1,1], "impl test 15 failed";

  var r16 := Hotelier("RRLRLLRL");
  expect r16 == [1,1,1,1,0,0,1,1,1,1], "impl test 16 failed";

  var r17 := Hotelier("RRRLLLRRR");
  expect r17 == [1,1,1,0,1,1,1,1,1,1], "impl test 17 failed";

  var r18 := Hotelier("LRRLRRLRRL");
  expect r18 == [1,1,1,1,1,1,1,1,1,1], "impl test 18 failed";

  var r19 := Hotelier("LLLLLLLLLL");
  expect r19 == [1,1,1,1,1,1,1,1,1,1], "impl test 19 failed";

  var r20 := Hotelier("LLLLLLL");
  expect r20 == [1,1,1,1,1,1,1,0,0,0], "impl test 20 failed";

  print "All tests passed\n";
}
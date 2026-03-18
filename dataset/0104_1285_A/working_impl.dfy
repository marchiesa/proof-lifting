method MezoPlayingZoma(s: string) returns (positions: int)
{
  var l := 0;
  var r := 0;
  for i := 0 to |s| {
    if s[i] == 'L' {
      l := l + 1;
    } else if s[i] == 'R' {
      r := r + 1;
    }
  }
  positions := l + r + 1;
}

method Main()
{
  var r1 := MezoPlayingZoma("LRLR");
  expect r1 == 5, "Test 1 failed";

  var r2 := MezoPlayingZoma("L");
  expect r2 == 2, "Test 2 failed";

  var r3 := MezoPlayingZoma("LRLLLLRRLLRLR");
  expect r3 == 14, "Test 3 failed";

  var r4 := MezoPlayingZoma("LR");
  expect r4 == 3, "Test 4 failed";

  var r5 := MezoPlayingZoma("R");
  expect r5 == 2, "Test 5 failed";

  var r6 := MezoPlayingZoma("LLLLLLLLLLLL");
  expect r6 == 13, "Test 6 failed";

  print "All tests passed\n";
}
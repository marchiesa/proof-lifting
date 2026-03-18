method HonestCoach(s: seq<int>) returns (minDiff: int)
{
  var a := s;
  // Sort (insertion sort)
  var i := 1;
  while i < |a|
  {
    var j := i;
    while j > 0 && a[j-1] > a[j]
    {
      var tmp := a[j-1];
      a := a[j-1 := a[j]][j := tmp];
      j := j - 1;
    }
    i := i + 1;
  }
  // Find minimum consecutive difference
  minDiff := a[1] - a[0];
  i := 2;
  while i < |a|
  {
    var diff := a[i] - a[i-1];
    if diff < minDiff {
      minDiff := diff;
    }
    i := i + 1;
  }
}

method Main()
{
  // Test 1
  var r1 := HonestCoach([3, 1, 2, 6, 4]);
  expect r1 == 1, "Test 1a failed";
  var r2 := HonestCoach([2, 1, 3, 2, 4, 3]);
  expect r2 == 0, "Test 1b failed";
  var r3 := HonestCoach([7, 9, 3, 1]);
  expect r3 == 2, "Test 1c failed";
  var r4 := HonestCoach([1, 1000]);
  expect r4 == 999, "Test 1d failed";
  var r5 := HonestCoach([100, 150, 200]);
  expect r5 == 50, "Test 1e failed";

  // Test 2
  var r6 := HonestCoach([5, 3]);
  expect r6 == 2, "Test 2a failed";
  var r7 := HonestCoach([1, 2, 3, 4]);
  expect r7 == 1, "Test 2b failed";
  var r8 := HonestCoach([10, 10, 10]);
  expect r8 == 0, "Test 2c failed";

  // Test 3
  var r9 := HonestCoach([7, 2]);
  expect r9 == 5, "Test 3 failed";

  // Test 4
  var r10 := HonestCoach([4, 1, 7, 3, 2]);
  expect r10 == 1, "Test 4a failed";
  var r11 := HonestCoach([50, 25, 1]);
  expect r11 == 24, "Test 4b failed";

  // Test 5
  var r12 := HonestCoach([5, 3, 8, 1, 9, 2, 7, 4, 6, 10]);
  expect r12 == 1, "Test 5 failed";

  // Test 6
  var r13 := HonestCoach([1, 1]);
  expect r13 == 0, "Test 6a failed";
  var r14 := HonestCoach([1, 2]);
  expect r14 == 1, "Test 6b failed";
  var r15 := HonestCoach([50, 1]);
  expect r15 == 49, "Test 6c failed";
  var r16 := HonestCoach([5, 5, 5]);
  expect r16 == 0, "Test 6d failed";

  // Test 7
  var r17 := HonestCoach([10, 20, 30, 40, 50, 15]);
  expect r17 == 5, "Test 7 failed";

  // Test 8
  var r18 := HonestCoach([3, 3, 3, 3, 3, 3, 3]);
  expect r18 == 0, "Test 8a failed";
  var r19 := HonestCoach([1, 1, 50, 50]);
  expect r19 == 0, "Test 8b failed";

  // Test 9
  var r20 := HonestCoach([1, 50, 25]);
  expect r20 == 24, "Test 9a failed";
  var r21 := HonestCoach([2, 4, 6, 8, 10]);
  expect r21 == 2, "Test 9b failed";
  var r22 := HonestCoach([42, 43]);
  expect r22 == 1, "Test 9c failed";

  // Test 10
  var r23 := HonestCoach([7, 1, 4, 9, 2, 8, 3, 6]);
  expect r23 == 1, "Test 10 failed";

  // Test 11
  var r24 := HonestCoach([1, 2]);
  expect r24 == 1, "Test 11a failed";
  var r25 := HonestCoach([5, 1, 3]);
  expect r25 == 2, "Test 11b failed";
  var r26 := HonestCoach([10, 20, 30, 40]);
  expect r26 == 10, "Test 11c failed";
  var r27 := HonestCoach([1, 1, 1, 1, 1]);
  expect r27 == 0, "Test 11d failed";
  var r28 := HonestCoach([3, 6, 9, 12, 15, 18]);
  expect r28 == 3, "Test 11e failed";

  print "All tests passed\n";
}
method FairDivision(a: seq<int>) returns (result: bool)
{
  var s := 0;
  var count1 := 0;
  var count2 := 0;
  var i := 0;
  while i < |a|
  {
    s := s + a[i];
    if a[i] == 1 {
      count1 := count1 + 1;
    }
    if a[i] == 2 {
      count2 := count2 + 1;
    }
    i := i + 1;
  }
  if s % 2 == 1 {
    return false;
  }
  if count2 % 2 == 1 && count1 == 0 {
    return false;
  }
  return true;
}

method Main()
{
  // Test 1 sub-cases
  var r1 := FairDivision([1, 1]);
  expect r1 == true, "Test 1a failed: [1,1] expected YES";

  var r2 := FairDivision([1, 2]);
  expect r2 == false, "Test 1b failed: [1,2] expected NO";

  var r3 := FairDivision([1, 2, 1, 2]);
  expect r3 == true, "Test 1c failed: [1,2,1,2] expected YES";

  var r4 := FairDivision([2, 2, 2]);
  expect r4 == false, "Test 1d failed: [2,2,2] expected NO";

  var r5 := FairDivision([2, 1, 2]);
  expect r5 == false, "Test 1e failed: [2,1,2] expected NO";

  // Test 2
  var r6 := FairDivision([1, 1]);
  expect r6 == true, "Test 2 failed: [1,1] expected YES";

  // Test 3
  var r7 := FairDivision([1, 2]);
  expect r7 == false, "Test 3 failed: [1,2] expected NO";

  // Test 4
  var r8 := FairDivision([1, 2, 1, 2]);
  expect r8 == true, "Test 4 failed: [1,2,1,2] expected YES";

  // Test 5
  var r9 := FairDivision([2, 2, 2]);
  expect r9 == false, "Test 5 failed: [2,2,2] expected NO";

  // Test 6
  var r10 := FairDivision([2, 2, 2, 1, 1, 1]);
  expect r10 == false, "Test 6 failed: [2,2,2,1,1,1] expected NO";

  // Test 7
  var r11 := FairDivision([1]);
  expect r11 == false, "Test 7 failed: [1] expected NO";

  // Test 8
  var r12 := FairDivision([2]);
  expect r12 == false, "Test 8 failed: [2] expected NO";

  // Test 9
  var r13 := FairDivision([1, 1, 1, 1, 2, 2, 2, 2]);
  expect r13 == true, "Test 9 failed: [1,1,1,1,2,2,2,2] expected YES";

  // Test 10
  var r14 := FairDivision([1, 1, 1, 2, 2]);
  expect r14 == false, "Test 10 failed: [1,1,1,2,2] expected NO";

  // Test 11
  var r15 := FairDivision([2, 2, 2, 2, 2, 1, 1, 1, 1, 1]);
  expect r15 == false, "Test 11 failed: [2,2,2,2,2,1,1,1,1,1] expected NO";

  print "All tests passed\n";
}
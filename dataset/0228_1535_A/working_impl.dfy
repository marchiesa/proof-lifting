method FairPlayoff(s1: int, s2: int, s3: int, s4: int) returns (fair: bool)
{
  var min12 := if s1 < s2 then s1 else s2;
  var max12 := if s1 > s2 then s1 else s2;
  var min34 := if s3 < s4 then s3 else s4;
  var max34 := if s3 > s4 then s3 else s4;

  if min34 > max12 || min12 > max34 {
    fair := false;
  } else {
    fair := true;
  }
}

method Main()
{
  var r: bool;

  // Test 1
  r := FairPlayoff(3, 7, 9, 5);
  expect r == true, "Test (3,7,9,5) expected YES";

  r := FairPlayoff(4, 5, 6, 9);
  expect r == false, "Test (4,5,6,9) expected NO";

  r := FairPlayoff(5, 3, 8, 1);
  expect r == true, "Test (5,3,8,1) expected YES";

  r := FairPlayoff(6, 5, 3, 2);
  expect r == false, "Test (6,5,3,2) expected NO";

  // Test 2
  r := FairPlayoff(8, 6, 2, 7);
  expect r == true, "Test (8,6,2,7) expected YES";

  // Test 7
  r := FairPlayoff(1, 2, 3, 4);
  expect r == false, "Test (1,2,3,4) expected NO";

  // Test 8
  r := FairPlayoff(10, 20, 30, 40);
  expect r == false, "Test (10,20,30,40) expected NO";

  // Test 9
  r := FairPlayoff(7, 3, 2, 8);
  expect r == true, "Test (7,3,2,8) expected YES";

  // Test 10
  r := FairPlayoff(50, 40, 30, 20);
  expect r == false, "Test (50,40,30,20) expected NO";

  // Test 11
  r := FairPlayoff(1, 3, 2, 4);
  expect r == true, "Test (1,3,2,4) expected YES";

  r := FairPlayoff(5, 10, 15, 20);
  expect r == false, "Test (5,10,15,20) expected NO";

  r := FairPlayoff(8, 2, 6, 4);
  expect r == true, "Test (8,2,6,4) expected YES";

  // Test 12
  r := FairPlayoff(1, 4, 2, 3);
  expect r == true, "Test (1,4,2,3) expected YES";

  r := FairPlayoff(9, 7, 5, 3);
  expect r == false, "Test (9,7,5,3) expected NO";

  r := FairPlayoff(2, 8, 6, 4);
  expect r == true, "Test (2,8,6,4) expected YES";

  r := FairPlayoff(10, 1, 5, 3);
  expect r == true, "Test (10,1,5,3) expected YES";

  r := FairPlayoff(7, 3, 9, 1);
  expect r == true, "Test (7,3,9,1) expected YES";

  print "All tests passed\n";
}
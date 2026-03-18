method AlexeyAndTrain(n: int, schedule: seq<(int, int)>, tm: seq<int>) returns (arrivalTime: int)
{
  var currentTime := 0;
  var prevB := 0;
  var i := 0;
  while i < n
  {
    var ai := schedule[i].0;
    var bi := schedule[i].1;
    var travelTime := ai - prevB + tm[i];
    currentTime := currentTime + travelTime;
    if i < n - 1 {
      var waitTime := bi - ai;
      currentTime := currentTime + (waitTime + 1) / 2;
      if currentTime < bi {
        currentTime := bi;
      }
    }
    prevB := bi;
    i := i + 1;
  }
  arrivalTime := currentTime;
}

method Main()
{
  // Test 1, case 1: n=2, schedule=[(2,4),(10,12)], tm=[0,2] → 12
  var r1 := AlexeyAndTrain(2, [(2,4),(10,12)], [0,2]);
  expect r1 == 12, "Test 1.1 failed";

  // Test 1, case 2: n=5, schedule=[(1,4),(7,8),(9,10),(13,15),(19,20)], tm=[1,2,3,4,5] → 32
  var r2 := AlexeyAndTrain(5, [(1,4),(7,8),(9,10),(13,15),(19,20)], [1,2,3,4,5]);
  expect r2 == 32, "Test 1.2 failed";

  // Test 2: n=1, schedule=[(1,8)], tm=[0] → 1
  var r3 := AlexeyAndTrain(1, [(1,8)], [0]);
  expect r3 == 1, "Test 2 failed";

  // Test 3: n=1, schedule=[(1,2)], tm=[0] → 1
  var r4 := AlexeyAndTrain(1, [(1,2)], [0]);
  expect r4 == 1, "Test 3 failed";

  // Test 4: n=1, schedule=[(3,5)], tm=[4] → 7
  var r5 := AlexeyAndTrain(1, [(3,5)], [4]);
  expect r5 == 7, "Test 4 failed";

  // Test 5: n=2, schedule=[(2,4),(10,12)], tm=[0,2] → 12
  var r6 := AlexeyAndTrain(2, [(2,4),(10,12)], [0,2]);
  expect r6 == 12, "Test 5 failed";

  // Test 6: n=3, schedule=[(1,3),(5,7),(9,11)], tm=[0,0,0] → 9
  var r7 := AlexeyAndTrain(3, [(1,3),(5,7),(9,11)], [0,0,0]);
  expect r7 == 9, "Test 6 failed";

  // Test 7: n=3, schedule=[(2,4),(6,8),(10,12)], tm=[1,1,1] → 11
  var r8 := AlexeyAndTrain(3, [(2,4),(6,8),(10,12)], [1,1,1]);
  expect r8 == 11, "Test 7 failed";

  // Test 8, case 1: n=1, schedule=[(1,2)], tm=[0] → 1
  var r9 := AlexeyAndTrain(1, [(1,2)], [0]);
  expect r9 == 1, "Test 8.1 failed";

  // Test 8, case 2: n=1, schedule=[(5,10)], tm=[3] → 8
  var r10 := AlexeyAndTrain(1, [(5,10)], [3]);
  expect r10 == 8, "Test 8.2 failed";

  // Test 9: n=4, schedule=[(1,2),(4,6),(8,10),(12,14)], tm=[0,1,2,3] → 16
  var r11 := AlexeyAndTrain(4, [(1,2),(4,6),(8,10),(12,14)], [0,1,2,3]);
  expect r11 == 16, "Test 9 failed";

  // Test 10, case 1: n=1, schedule=[(1,3)], tm=[0] → 1
  var r12 := AlexeyAndTrain(1, [(1,3)], [0]);
  expect r12 == 1, "Test 10.1 failed";

  // Test 10, case 2: n=2, schedule=[(1,2),(5,8)], tm=[1,0] → 6
  var r13 := AlexeyAndTrain(2, [(1,2),(5,8)], [1,0]);
  expect r13 == 6, "Test 10.2 failed";

  // Test 10, case 3: n=1, schedule=[(10,20)], tm=[5] → 15
  var r14 := AlexeyAndTrain(1, [(10,20)], [5]);
  expect r14 == 15, "Test 10.3 failed";

  // Test 11: n=5, schedule=[(1,3),(5,7),(9,11),(13,15),(17,19)], tm=[2,2,2,2,2] → 23
  var r15 := AlexeyAndTrain(5, [(1,3),(5,7),(9,11),(13,15),(17,19)], [2,2,2,2,2]);
  expect r15 == 23, "Test 11 failed";

  // Test 12: n=10, schedule=[(1,2),(4,5),(7,8),(10,11),(13,14),(16,17),(19,20),(22,23),(25,26),(28,30)], tm=[0,0,0,0,0,0,0,0,0,0] → 28
  var r16 := AlexeyAndTrain(10, [(1,2),(4,5),(7,8),(10,11),(13,14),(16,17),(19,20),(22,23),(25,26),(28,30)], [0,0,0,0,0,0,0,0,0,0]);
  expect r16 == 28, "Test 12 failed";

  print "All tests passed\n";
}
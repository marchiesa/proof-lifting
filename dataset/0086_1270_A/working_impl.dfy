method CardGame(n: int, k1: int, k2: int, a: seq<int>, b: seq<int>) returns (firstPlayerWins: bool)
{
  var maxA := a[0];
  var i := 1;
  while i < |a|
  {
    if a[i] > maxA {
      maxA := a[i];
    }
    i := i + 1;
  }

  var maxB := b[0];
  var j := 1;
  while j < |b|
  {
    if b[j] > maxB {
      maxB := b[j];
    }
    j := j + 1;
  }

  firstPlayerWins := maxA > maxB;
}

method Main()
{
  // Test 1, TC1: n=2, k1=1, k2=1, a=[2], b=[1] → YES
  var r1 := CardGame(2, 1, 1, [2], [1]);
  expect r1 == true, "Test 1.1 failed";

  // Test 1, TC2: n=5, k1=2, k2=3, a=[2,3], b=[1,4,5] → NO
  var r2 := CardGame(5, 2, 3, [2, 3], [1, 4, 5]);
  expect r2 == false, "Test 1.2 failed";

  // Test 2: n=2, k1=1, k2=1, a=[1], b=[2] → NO
  var r3 := CardGame(2, 1, 1, [1], [2]);
  expect r3 == false, "Test 2 failed";

  // Test 3: n=3, k1=2, k2=1, a=[1,3], b=[2] → YES
  var r4 := CardGame(3, 2, 1, [1, 3], [2]);
  expect r4 == true, "Test 3 failed";

  // Test 4: n=4, k1=2, k2=2, a=[2,4], b=[1,3] → YES
  var r5 := CardGame(4, 2, 2, [2, 4], [1, 3]);
  expect r5 == true, "Test 4 failed";

  // Test 5: n=5, k1=3, k2=2, a=[1,2,5], b=[3,4] → YES
  var r6 := CardGame(5, 3, 2, [1, 2, 5], [3, 4]);
  expect r6 == true, "Test 5 failed";

  // Test 6: n=6, k1=1, k2=5, a=[6], b=[1,2,3,4,5] → YES
  var r7 := CardGame(6, 1, 5, [6], [1, 2, 3, 4, 5]);
  expect r7 == true, "Test 6 failed";

  // Test 7: n=10, k1=5, k2=5, a=[2,4,6,8,10], b=[1,3,5,7,9] → YES
  var r8 := CardGame(10, 5, 5, [2, 4, 6, 8, 10], [1, 3, 5, 7, 9]);
  expect r8 == true, "Test 7 failed";

  // Test 8, TC1: n=2, k1=1, k2=1, a=[2], b=[1] → YES
  var r9 := CardGame(2, 1, 1, [2], [1]);
  expect r9 == true, "Test 8.1 failed";

  // Test 8, TC2: n=3, k1=1, k2=2, a=[3], b=[1,2] → YES
  var r10 := CardGame(3, 1, 2, [3], [1, 2]);
  expect r10 == true, "Test 8.2 failed";

  // Test 8, TC3: n=4, k1=3, k2=1, a=[1,2,4], b=[3] → YES
  var r11 := CardGame(4, 3, 1, [1, 2, 4], [3]);
  expect r11 == true, "Test 8.3 failed";

  // Test 9: n=7, k1=4, k2=3, a=[1,3,5,7], b=[2,4,6] → YES
  var r12 := CardGame(7, 4, 3, [1, 3, 5, 7], [2, 4, 6]);
  expect r12 == true, "Test 9 failed";

  // Test 10, TC1: n=5, k1=2, k2=3, a=[2,3], b=[1,4,5] → NO
  var r13 := CardGame(5, 2, 3, [2, 3], [1, 4, 5]);
  expect r13 == false, "Test 10.1 failed";

  // Test 10, TC2: n=5, k1=1, k2=4, a=[5], b=[1,2,3,4] → YES
  var r14 := CardGame(5, 1, 4, [5], [1, 2, 3, 4]);
  expect r14 == true, "Test 10.2 failed";

  // Test 11: n=8, k1=3, k2=5, a=[1,4,8], b=[2,3,5,6,7] → YES
  var r15 := CardGame(8, 3, 5, [1, 4, 8], [2, 3, 5, 6, 7]);
  expect r15 == true, "Test 11 failed";

  print "All tests passed\n";
}
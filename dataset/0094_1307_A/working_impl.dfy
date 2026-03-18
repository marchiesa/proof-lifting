method CowAndHaybales(a: seq<int>, d: int) returns (result: int)
{
  var n := |a|;
  var arr := new int[n];
  var Asum := 0;
  for k := 0 to n {
    arr[k] := a[k];
    Asum := Asum + a[k];
  }
  var remaining := d;
  while remaining > 0 && arr[0] != Asum
    decreases remaining
  {
    var i := 1;
    while i < n && arr[i] == 0
      decreases n - i
    {
      i := i + 1;
    }
    if i < n {
      arr[i - 1] := arr[i - 1] + 1;
      arr[i] := arr[i] - 1;
    }
    remaining := remaining - 1;
  }
  result := arr[0];
}

method Main()
{
  // Test 1, case 1: n=4, d=5, a=[1,0,3,2] -> 3
  var r1 := CowAndHaybales([1, 0, 3, 2], 5);
  expect r1 == 3, "Test 1.1 failed";

  // Test 1, case 2: n=2, d=2, a=[100,1] -> 101
  var r2 := CowAndHaybales([100, 1], 2);
  expect r2 == 101, "Test 1.2 failed";

  // Test 1, case 3: n=1, d=8, a=[0] -> 0
  var r3 := CowAndHaybales([0], 8);
  expect r3 == 0, "Test 1.3 failed";

  // Test 2: n=3, d=10, a=[5,3,2] -> 10
  var r4 := CowAndHaybales([5, 3, 2], 10);
  expect r4 == 10, "Test 2 failed";

  // Test 3: n=1, d=5, a=[7] -> 7
  var r5 := CowAndHaybales([7], 5);
  expect r5 == 7, "Test 3 failed";

  // Test 4: n=5, d=3, a=[0,0,0,0,10] -> 0
  var r6 := CowAndHaybales([0, 0, 0, 0, 10], 3);
  expect r6 == 0, "Test 4 failed";

  // Test 5: n=2, d=1, a=[0,50] -> 1
  var r7 := CowAndHaybales([0, 50], 1);
  expect r7 == 1, "Test 5 failed";

  // Test 6: n=4, d=20, a=[1,1,1,1] -> 4
  var r8 := CowAndHaybales([1, 1, 1, 1], 20);
  expect r8 == 4, "Test 6 failed";

  // Test 7: n=3, d=0, a=[10,20,30] -> 10
  var r9 := CowAndHaybales([10, 20, 30], 0);
  expect r9 == 10, "Test 7 failed";

  // Test 8: n=1, d=1, a=[0] -> 0
  var r10 := CowAndHaybales([0], 1);
  expect r10 == 0, "Test 8 failed";

  // Test 9, case 1: n=3, d=6, a=[2,4,3] -> 7
  var r11 := CowAndHaybales([2, 4, 3], 6);
  expect r11 == 7, "Test 9.1 failed";

  // Test 9, case 2: n=2, d=100, a=[0,0] -> 0
  var r12 := CowAndHaybales([0, 0], 100);
  expect r12 == 0, "Test 9.2 failed";

  // Test 10: n=5, d=50, a=[10,10,10,10,10] -> 36
  var r13 := CowAndHaybales([10, 10, 10, 10, 10], 50);
  expect r13 == 36, "Test 10 failed";

  // Test 11: n=10, d=5, a=[0,1,2,3,4,5,6,7,8,9] -> 3
  var r14 := CowAndHaybales([0, 1, 2, 3, 4, 5, 6, 7, 8, 9], 5);
  expect r14 == 3, "Test 11 failed";

  print "All tests passed\n";
}
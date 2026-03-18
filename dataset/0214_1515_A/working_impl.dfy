method PhoenixAndGold(n: int, x: int, w: seq<int>) returns (possible: bool, order: seq<int>)
{
  var s := 0;
  var i := 0;
  while i < |w| {
    s := s + w[i];
    i := i + 1;
  }

  if s == x {
    possible := false;
    order := [];
    return;
  }

  possible := true;
  var ww := w;
  var remaining := x;
  order := [];

  i := 0;
  while i < n {
    if ww[|ww| - 1] == remaining {
      var a := ww[|ww| - 1];
      var b := ww[|ww| - 2];
      ww := ww[..|ww| - 2] + [a] + [b];
    }
    var y := ww[|ww| - 1];
    ww := ww[..|ww| - 1];
    remaining := remaining - y;
    order := order + [y];
    i := i + 1;
  }
}

method Main()
{
  // Test 1, case 1: n=3, x=2, w=[3,2,1] → true, [1,2,3]
  var p1, o1 := PhoenixAndGold(3, 2, [3, 2, 1]);
  expect p1 == true;
  expect o1 == [1, 2, 3];

  // Test 1, case 2: n=5, x=3, w=[1,2,3,4,8] → true, [8,4,3,2,1]
  var p2, o2 := PhoenixAndGold(5, 3, [1, 2, 3, 4, 8]);
  expect p2 == true;
  expect o2 == [8, 4, 3, 2, 1];

  // Test 1, case 3: n=1, x=5, w=[5] → false
  var p3, o3 := PhoenixAndGold(1, 5, [5]);
  expect p3 == false;

  // Test 2: n=6, x=46, w=[10,11,12,13,21,25] → true, [25,13,21,12,11,10]
  var p4, o4 := PhoenixAndGold(6, 46, [10, 11, 12, 13, 21, 25]);
  expect p4 == true;
  expect o4 == [25, 13, 21, 12, 11, 10];

  // Test 3: n=3, x=2, w=[3,2,1] → true, [1,2,3]
  var p5, o5 := PhoenixAndGold(3, 2, [3, 2, 1]);
  expect p5 == true;
  expect o5 == [1, 2, 3];

  // Test 4: n=5, x=10, w=[1,2,3,4,5] → true, [5,4,3,2,1]
  var p6, o6 := PhoenixAndGold(5, 10, [1, 2, 3, 4, 5]);
  expect p6 == true;
  expect o6 == [5, 4, 3, 2, 1];

  // Test 5: n=1, x=5, w=[5] → false
  var p7, o7 := PhoenixAndGold(1, 5, [5]);
  expect p7 == false;

  // Test 6: n=4, x=6, w=[1,3,2,4] → true, [4,3,2,1]
  var p8, o8 := PhoenixAndGold(4, 6, [1, 3, 2, 4]);
  expect p8 == true;
  expect o8 == [4, 3, 2, 1];

  // Test 7: n=1, x=1, w=[1] → false
  var p9, o9 := PhoenixAndGold(1, 1, [1]);
  expect p9 == false;

  // Test 8, case 1: n=3, x=3, w=[1,2,3] → true, [2,3,1]
  var p10, o10 := PhoenixAndGold(3, 3, [1, 2, 3]);
  expect p10 == true;
  expect o10 == [2, 3, 1];

  // Test 8, case 2: n=2, x=7, w=[4,3] → false
  var p11, o11 := PhoenixAndGold(2, 7, [4, 3]);
  expect p11 == false;

  // Test 9: n=6, x=15, w=[5,4,3,2,1,6] → true, [6,1,2,3,4,5]
  var p12, o12 := PhoenixAndGold(6, 15, [5, 4, 3, 2, 1, 6]);
  expect p12 == true;
  expect o12 == [6, 1, 2, 3, 4, 5];

  // Test 10: n=10, x=50, w=[1,2,3,4,5,6,7,8,9,10] → true, [10,9,8,7,6,5,4,3,2,1]
  var p13, o13 := PhoenixAndGold(10, 50, [1, 2, 3, 4, 5, 6, 7, 8, 9, 10]);
  expect p13 == true;
  expect o13 == [10, 9, 8, 7, 6, 5, 4, 3, 2, 1];

  // Test 11: n=3, x=100, w=[10,20,30] → true, [30,20,10]
  var p14, o14 := PhoenixAndGold(3, 100, [10, 20, 30]);
  expect p14 == true;
  expect o14 == [30, 20, 10];

  // Test 12, case 1: n=2, x=3, w=[1,2] → false
  var p15, o15 := PhoenixAndGold(2, 3, [1, 2]);
  expect p15 == false;

  // Test 12, case 2: n=4, x=10, w=[1,2,3,4] → false
  var p16, o16 := PhoenixAndGold(4, 10, [1, 2, 3, 4]);
  expect p16 == false;

  // Test 12, case 3: n=1, x=7, w=[7] → false
  var p17, o17 := PhoenixAndGold(1, 7, [7]);
  expect p17 == false;

  print "All tests passed\n";
}
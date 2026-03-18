method NekoFindsGrapes(a: seq<int>, b: seq<int>) returns (maxChests: int)
{
  var a0 := 0;
  var a1 := 0;
  var b0 := 0;
  var b1 := 0;

  var i := 0;
  while i < |a|
  {
    if a[i] % 2 == 0 {
      a0 := a0 + 1;
    } else {
      a1 := a1 + 1;
    }
    i := i + 1;
  }

  i := 0;
  while i < |b|
  {
    if b[i] % 2 == 0 {
      b0 := b0 + 1;
    } else {
      b1 := b1 + 1;
    }
    i := i + 1;
  }

  var x := if a0 < b1 then a0 else b1;
  var y := if a1 < b0 then a1 else b0;
  maxChests := x + y;
}

method Main()
{
  var result: int;

  // Test 1
  result := NekoFindsGrapes([9, 14, 6, 2, 11], [8, 4, 7, 20]);
  expect result == 3, "Test 1 failed";

  // Test 2
  result := NekoFindsGrapes([2, 4, 6, 8, 10], [5]);
  expect result == 1, "Test 2 failed";

  // Test 3
  result := NekoFindsGrapes([10], [20, 30, 40, 50]);
  expect result == 0, "Test 3 failed";

  // Test 4
  result := NekoFindsGrapes(
    [72, 105, 100, 105, 110, 103, 32, 109, 101, 115, 115, 97, 103, 101, 115, 32, 105, 110, 32, 116, 101, 115, 116, 99, 97, 115, 101],
    [83, 110, 101, 97, 107, 32, 49, 48, 48]
  );
  expect result == 9, "Test 4 failed";

  // Test 5
  result := NekoFindsGrapes([107, 117, 110], [71, 114, 101, 101, 110, 71, 114, 97, 112, 101]);
  expect result == 3, "Test 5 failed";

  // Test 6
  result := NekoFindsGrapes([116, 111, 117, 114, 105, 115, 116], [112, 101, 116, 114]);
  expect result == 4, "Test 6 failed";

  // Test 7
  result := NekoFindsGrapes(
    [522312461, 931001459, 598654597, 488228616, 544064902, 21923894, 329635457, 980089248, 988262691, 654502493],
    [967529230, 543358150, 835120075, 128123793, 809901567, 613170206, 152157661, 479980560, 859252956, 318029856]
  );
  expect result == 10, "Test 7 failed";

  // Test 8
  result := NekoFindsGrapes([1], [1, 2, 3, 4, 5, 6, 7, 8, 9, 10]);
  expect result == 1, "Test 8 failed";

  // Test 9
  result := NekoFindsGrapes([1, 2, 3, 4, 5], [1]);
  expect result == 1, "Test 9 failed";

  // Test 10
  result := NekoFindsGrapes([2, 2, 1, 1, 1, 1, 1], [2, 2, 2, 1]);
  expect result == 4, "Test 10 failed";

  // Test 11
  result := NekoFindsGrapes([1, 1, 1, 2], [2]);
  expect result == 1, "Test 11 failed";

  // Test 12
  result := NekoFindsGrapes([3, 5, 7, 8], [2]);
  expect result == 1, "Test 12 failed";

  // Test 13
  result := NekoFindsGrapes([1, 2, 2, 2, 2], [1, 1]);
  expect result == 2, "Test 13 failed";

  // Test 14
  result := NekoFindsGrapes([3, 2, 1, 4], [2, 3]);
  expect result == 2, "Test 14 failed";

  // Test 15
  result := NekoFindsGrapes([1, 2], [1, 1, 2, 2]);
  expect result == 2, "Test 15 failed";

  // Test 16
  result := NekoFindsGrapes([2, 2, 3, 3], [2]);
  expect result == 1, "Test 16 failed";

  // Test 17
  result := NekoFindsGrapes([2, 2, 2, 3, 3], [3]);
  expect result == 1, "Test 17 failed";

  // Test 18
  result := NekoFindsGrapes([1, 1, 2, 2], [2]);
  expect result == 1, "Test 18 failed";

  // Test 19
  result := NekoFindsGrapes([3], [3, 4, 4, 4, 4]);
  expect result == 1, "Test 19 failed";

  // Test 20
  result := NekoFindsGrapes([2, 4, 6, 1, 3, 5], [8, 10, 7, 9]);
  expect result == 4, "Test 20 failed";

  print "All tests passed\n";
}
// Maximum Length Chain of Pairs -- Spec tests

function Max(a: int, b: int): int { if a >= b then a else b }

method MaxChainLength(pairs: seq<(int, int)>) returns (result: int)
  requires |pairs| > 0
  requires forall k :: 0 <= k < |pairs| ==> pairs[k].0 < pairs[k].1
  ensures result >= 1
{
  var dp := new int[|pairs|];
  var i := 0;
  while i < |pairs|
    invariant 0 <= i <= |pairs|
    invariant forall k :: 0 <= k < i ==> dp[k] >= 1
    decreases |pairs| - i
  {
    dp[i] := 1;
    var j := 0;
    while j < i invariant 0 <= j <= i invariant dp[i] >= 1 invariant forall k :: 0 <= k < i ==> dp[k] >= 1 decreases i - j {
      if pairs[j].1 < pairs[i].0 { dp[i] := Max(dp[i], dp[j] + 1); }
      j := j + 1;
    }
    i := i + 1;
  }
  result := dp[0];
  i := 1;
  while i < |pairs| invariant 1 <= i <= |pairs| invariant result >= 1 decreases |pairs| - i {
    result := Max(result, dp[i]);
    i := i + 1;
  }
}

method Main() {
  var r1 := MaxChainLength([(5, 24), (15, 25), (27, 40)]);
  expect r1 == 2;

  var r2 := MaxChainLength([(1, 2), (3, 4), (5, 6)]);
  expect r2 == 3;

  var r3 := MaxChainLength([(1, 100)]);
  expect r3 == 1;

  var r4 := MaxChainLength([(1, 10), (2, 9), (3, 8)]);
  expect r4 == 1;

  expect r3 >= 1;

  print "All spec tests passed\n";
}

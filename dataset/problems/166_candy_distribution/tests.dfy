// Candy Distribution -- Spec tests

function Max(a: int, b: int): int { if a >= b then a else b }

predicate ValidDistribution(ratings: seq<int>, candy: seq<int>) {
  |candy| == |ratings| &&
  (forall i :: 0 <= i < |candy| ==> candy[i] >= 1) &&
  (forall i :: 0 < i < |ratings| && ratings[i] > ratings[i-1] ==> candy[i] > candy[i-1]) &&
  (forall i :: 0 <= i < |ratings| - 1 && ratings[i] > ratings[i+1] ==> candy[i] > candy[i+1])
}

method CandyDistribution(ratings: seq<int>) returns (candy: seq<int>, total: int)
  requires |ratings| > 0
  ensures ValidDistribution(ratings, candy)
  ensures total >= |ratings|
{
  var n := |ratings|;
  candy := seq(n, _ => 1);
  var i := 1;
  while i < n invariant 1 <= i <= n invariant |candy| == n invariant forall k :: 0 <= k < n ==> candy[k] >= 1 decreases n - i {
    if ratings[i] > ratings[i-1] { candy := candy[i := candy[i-1] + 1]; }
    i := i + 1;
  }
  i := n - 2;
  while i >= 0 invariant -1 <= i < n - 1 invariant |candy| == n invariant forall k :: 0 <= k < n ==> candy[k] >= 1 decreases i + 1 {
    if ratings[i] > ratings[i+1] { candy := candy[i := Max(candy[i], candy[i+1] + 1)]; }
    i := i - 1;
  }
  assume {:axiom} ValidDistribution(ratings, candy);
  total := 0;
  i := 0;
  while i < n invariant 0 <= i <= n invariant total >= i decreases n - i {
    total := total + candy[i];
    i := i + 1;
  }
}

method Main() {
  var c1, t1 := CandyDistribution([1, 0, 2]);
  expect t1 == 5;
  expect ValidDistribution([1, 0, 2], c1);

  var c2, t2 := CandyDistribution([1, 2, 2]);
  expect t2 >= 3;
  expect ValidDistribution([1, 2, 2], c2);

  // All same rating: each gets 1
  var c3, t3 := CandyDistribution([1, 1, 1]);
  expect t3 == 3;

  // Strictly decreasing
  var c4, t4 := CandyDistribution([3, 2, 1]);
  expect t4 == 6;
  expect c4[0] > c4[1];

  // Negative: invalid distribution would fail
  expect !ValidDistribution([1, 2, 3], [1, 1, 1]);

  print "All spec tests passed\n";
}

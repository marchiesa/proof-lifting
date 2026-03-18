function Sum(a: seq<int>): int
  decreases |a|
{
  if |a| == 0 then 0 else Sum(a[..|a|-1]) + a[|a|-1]
}

predicate AllDistinct(a: seq<int>)
{
  forall i, j | 0 <= i < |a| && 0 <= j < |a| && i != j :: a[i] != a[j]
}

predicate IsPermutation(a: seq<int>, b: seq<int>)
{
  multiset(a) == multiset(b)
}

predicate NoPrefixSumEquals(a: seq<int>, x: int)
{
  forall i | 1 <= i <= |a| :: Sum(a[..i]) != x
}

predicate CanComplete(placed: seq<int>, remaining: seq<int>, x: int)
  decreases |remaining|
{
  if |remaining| == 0 then
    true
  else
    exists i | 0 <= i < |remaining| ::
      Sum(placed) + remaining[i] != x
      && CanComplete(
           placed + [remaining[i]],
           remaining[..i] + remaining[i+1..],
           x
         )
}

predicate ExistsValidOrdering(w: seq<int>, x: int)
{
  CanComplete([], w, x)
}

method PhoenixAndGold(n: int, x: int, w: seq<int>) returns (possible: bool, order: seq<int>)
  requires n == |w|
  requires n >= 1
  requires AllDistinct(w)
  ensures possible <==> ExistsValidOrdering(w, x)
  ensures possible ==> IsPermutation(order, w) && NoPrefixSumEquals(order, x)
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
  // ============================================================
  // SPEC POSITIVE TESTS (small inputs, testing ensures predicates)
  // ============================================================

  // Spec pos 1 (from Test 1c/5): w=[5], x=5 -> possible=false
  expect !ExistsValidOrdering([5], 5), "spec positive 1";

  // Spec pos 2 (from Test 7): w=[1], x=1 -> possible=false
  expect !ExistsValidOrdering([1], 1), "spec positive 2";

  // Spec pos 3 (from Test 1a/3): w=[3,2,1], x=2 -> possible=true, order=[1,2,3]
  expect ExistsValidOrdering([3, 2, 1], 2), "spec positive 3a";
  expect IsPermutation([1, 2, 3], [3, 2, 1]), "spec positive 3b";
  expect NoPrefixSumEquals([1, 2, 3], 2), "spec positive 3c";

  // Spec pos 4 (from Test 8a): w=[1,2,3], x=3 -> possible=true, order=[2,3,1]
  expect ExistsValidOrdering([1, 2, 3], 3), "spec positive 4a";
  expect IsPermutation([2, 3, 1], [1, 2, 3]), "spec positive 4b";
  expect NoPrefixSumEquals([2, 3, 1], 3), "spec positive 4c";

  // Spec pos 5 (from Test 8b): w=[4,3], x=7 -> possible=false
  expect !ExistsValidOrdering([4, 3], 7), "spec positive 5";

  // Spec pos 6 (from Test 12a): w=[1,2], x=3 -> possible=false
  expect !ExistsValidOrdering([1, 2], 3), "spec positive 6";

  // Spec pos 7 (from Test 12c): w=[7], x=7 -> possible=false
  expect !ExistsValidOrdering([7], 7), "spec positive 7";

  // ============================================================
  // SPEC NEGATIVE TESTS (small inputs, wrong outputs rejected)
  // ============================================================

  // Spec neg 1 (from Neg 1): w=[5], x=5 -- wrong claims possible=true
  expect !ExistsValidOrdering([5], 5), "spec negative 1";

  // Spec neg 2 (from Neg 2, scaled to len 3): w=[1,2,3], x=2, wrong order [2,3,1]
  //   Sum([2])=2=x so NoPrefixSumEquals fails
  expect !(IsPermutation([2, 3, 1], [1, 2, 3]) && NoPrefixSumEquals([2, 3, 1], 2)), "spec negative 2";

  // Spec neg 3 (from Neg 3): w=[3,2,1], x=2, wrong order [2,1,3]
  //   Sum([2])=2=x so NoPrefixSumEquals fails
  expect !(IsPermutation([2, 1, 3], [3, 2, 1]) && NoPrefixSumEquals([2, 1, 3], 2)), "spec negative 3";

  // Spec neg 4 (from Neg 4, scaled to len 3): w=[1,2,3], x=3, wrong order [1,2,3]
  //   Sum([1,2])=3=x so NoPrefixSumEquals fails
  expect !(IsPermutation([1, 2, 3], [1, 2, 3]) && NoPrefixSumEquals([1, 2, 3], 3)), "spec negative 4";

  // Spec neg 5 (from Neg 5): w=[5], x=5, wrong claims possible=true with order [5]
  //   Sum([5])=5=x so NoPrefixSumEquals fails
  expect !NoPrefixSumEquals([5], 5), "spec negative 5";

  // Spec neg 6 (from Neg 6, scaled to len 2): w=[1,2], x=3, wrong order [2,1]
  //   Sum([2,1])=3=x so NoPrefixSumEquals fails
  expect !(IsPermutation([2, 1], [1, 2]) && NoPrefixSumEquals([2, 1], 3)), "spec negative 6";

  // Spec neg 7 (from Neg 7): w=[1], x=1, wrong claims possible=true with order [1]
  //   Sum([1])=1=x so NoPrefixSumEquals fails
  expect !NoPrefixSumEquals([1], 1), "spec negative 7";

  // Spec neg 8 (from Neg 8): w=[4,3], x=7, wrong claims possible=true
  expect !ExistsValidOrdering([4, 3], 7), "spec negative 8";

  // Spec neg 9 (from Neg 9, scaled to len 3): w=[1,2,3], x=6, wrong order [3,2,1]
  //   Sum([3,2,1])=6=x so NoPrefixSumEquals fails
  expect !(IsPermutation([3, 2, 1], [1, 2, 3]) && NoPrefixSumEquals([3, 2, 1], 6)), "spec negative 9";

  // Spec neg 10 (from Neg 10, scaled to len 3): w=[1,2,3], x=6, wrong order [1,2,3]
  //   Sum([1,2,3])=6=x so NoPrefixSumEquals fails
  expect !(IsPermutation([1, 2, 3], [1, 2, 3]) && NoPrefixSumEquals([1, 2, 3], 6)), "spec negative 10";

  // ============================================================
  // IMPLEMENTATION TESTS (full-size inputs)
  // ============================================================

  // Impl test 1 (Test 1a): n=3, x=2, w=[3,2,1]
  var p1, o1 := PhoenixAndGold(3, 2, [3, 2, 1]);
  expect p1 == true, "impl test 1 failed";
  expect o1 == [1, 2, 3], "impl test 1 order failed";

  // Impl test 2 (Test 1b): n=5, x=3, w=[1,2,3,4,8]
  var p2, o2 := PhoenixAndGold(5, 3, [1, 2, 3, 4, 8]);
  expect p2 == true, "impl test 2 failed";
  expect o2 == [8, 4, 3, 2, 1], "impl test 2 order failed";

  // Impl test 3 (Test 1c): n=1, x=5, w=[5]
  var p3, o3 := PhoenixAndGold(1, 5, [5]);
  expect p3 == false, "impl test 3 failed";

  // Impl test 4 (Test 2): n=6, x=46, w=[10,11,12,13,21,25]
  var p4, o4 := PhoenixAndGold(6, 46, [10, 11, 12, 13, 21, 25]);
  expect p4 == true, "impl test 4 failed";
  expect o4 == [25, 13, 21, 12, 11, 10], "impl test 4 order failed";

  // Impl test 5 (Test 3): n=3, x=2, w=[3,2,1]
  var p5, o5 := PhoenixAndGold(3, 2, [3, 2, 1]);
  expect p5 == true, "impl test 5 failed";
  expect o5 == [1, 2, 3], "impl test 5 order failed";

  // Impl test 6 (Test 4): n=5, x=10, w=[1,2,3,4,5]
  var p6, o6 := PhoenixAndGold(5, 10, [1, 2, 3, 4, 5]);
  expect p6 == true, "impl test 6 failed";
  expect o6 == [5, 4, 3, 2, 1], "impl test 6 order failed";

  // Impl test 7 (Test 5): n=1, x=5, w=[5]
  var p7, o7 := PhoenixAndGold(1, 5, [5]);
  expect p7 == false, "impl test 7 failed";

  // Impl test 8 (Test 6): n=4, x=6, w=[1,3,2,4]
  var p8, o8 := PhoenixAndGold(4, 6, [1, 3, 2, 4]);
  expect p8 == true, "impl test 8 failed";
  expect o8 == [4, 3, 2, 1], "impl test 8 order failed";

  // Impl test 9 (Test 7): n=1, x=1, w=[1]
  var p9, o9 := PhoenixAndGold(1, 1, [1]);
  expect p9 == false, "impl test 9 failed";

  // Impl test 10 (Test 8a): n=3, x=3, w=[1,2,3]
  var p10, o10 := PhoenixAndGold(3, 3, [1, 2, 3]);
  expect p10 == true, "impl test 10 failed";
  expect o10 == [2, 3, 1], "impl test 10 order failed";

  // Impl test 11 (Test 8b): n=2, x=7, w=[4,3]
  var p11, o11 := PhoenixAndGold(2, 7, [4, 3]);
  expect p11 == false, "impl test 11 failed";

  // Impl test 12 (Test 9): n=6, x=15, w=[5,4,3,2,1,6]
  var p12, o12 := PhoenixAndGold(6, 15, [5, 4, 3, 2, 1, 6]);
  expect p12 == true, "impl test 12 failed";
  expect o12 == [6, 1, 2, 3, 4, 5], "impl test 12 order failed";

  // Impl test 13 (Test 10): n=10, x=50, w=[1,2,3,4,5,6,7,8,9,10]
  var p13, o13 := PhoenixAndGold(10, 50, [1, 2, 3, 4, 5, 6, 7, 8, 9, 10]);
  expect p13 == true, "impl test 13 failed";
  expect o13 == [10, 9, 8, 7, 6, 5, 4, 3, 2, 1], "impl test 13 order failed";

  // Impl test 14 (Test 11): n=3, x=100, w=[10,20,30]
  var p14, o14 := PhoenixAndGold(3, 100, [10, 20, 30]);
  expect p14 == true, "impl test 14 failed";
  expect o14 == [30, 20, 10], "impl test 14 order failed";

  // Impl test 15 (Test 12a): n=2, x=3, w=[1,2]
  var p15, o15 := PhoenixAndGold(2, 3, [1, 2]);
  expect p15 == false, "impl test 15 failed";

  // Impl test 16 (Test 12b): n=4, x=10, w=[1,2,3,4]
  var p16, o16 := PhoenixAndGold(4, 10, [1, 2, 3, 4]);
  expect p16 == false, "impl test 16 failed";

  // Impl test 17 (Test 12c): n=1, x=7, w=[7]
  var p17, o17 := PhoenixAndGold(1, 7, [7]);
  expect p17 == false, "impl test 17 failed";

  print "All tests passed\n";
}
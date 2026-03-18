ghost function Sum(a: seq<int>): int
  decreases |a|
{
  if |a| == 0 then 0 else Sum(a[..|a|-1]) + a[|a|-1]
}

ghost predicate AllDistinct(a: seq<int>)
{
  forall i, j | 0 <= i < |a| && 0 <= j < |a| && i != j :: a[i] != a[j]
}

ghost predicate IsPermutation(a: seq<int>, b: seq<int>)
{
  multiset(a) == multiset(b)
}

// Verify that a specific placement order never causes the scale to show weight x
ghost predicate NoPrefixSumEquals(a: seq<int>, x: int)
{
  forall i | 1 <= i <= |a| :: Sum(a[..i]) != x
}

// Operational model of the placement process:
// Given pieces already on the scale (`placed`), can we place all `remaining`
// pieces one at a time — each time choosing which piece to place next —
// such that the scale's total never equals x?
ghost predicate CanComplete(placed: seq<int>, remaining: seq<int>, x: int)
  decreases |remaining|
{
  if |remaining| == 0 then
    true
  else
    // Try each remaining piece as the next one to place
    exists i | 0 <= i < |remaining| ::
      // Placing remaining[i] must not make the total equal x
      Sum(placed) + remaining[i] != x
      // And we can successfully place all pieces after this choice
      && CanComplete(
           placed + [remaining[i]],
           remaining[..i] + remaining[i+1..],
           x
         )
}

// Starting from an empty scale, can all pieces in w be placed
// one at a time without the total ever reaching x?
ghost predicate ExistsValidOrdering(w: seq<int>, x: int)
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
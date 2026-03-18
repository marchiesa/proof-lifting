// ---- FORMAL SPECIFICATION ----

// Physics: bottom train b is at grid position (b, T) at time T.
// Left train l is at grid position (T, l) at time T.
// Two trains collide when they occupy the same position at the same time:
// (b, T) == (T, l) for some time T in [0, 101].
ghost predicate TrainsCollide(b: int, l: int) {
  exists T :: b == T && l == T
}

// All elements in a sequence are distinct (each train number is unique)
ghost predicate AllDistinct(s: seq<int>) {
  forall i | 0 <= i < |s| ::
    forall j | i + 1 <= j < |s| ::
      s[i] != s[j]
}

// Enumerate all collision pairs: (bottom_index, left_index) where trains collide
ghost function CollisionPairsForOne(bi: int, bval: int, left: seq<int>): seq<(int, int)>
  decreases |left|
{
  if |left| == 0 then []
  else
    CollisionPairsForOne(bi, bval, left[..|left| - 1]) +
    (if TrainsCollide(bval, left[|left| - 1]) then [(bi, |left| - 1)] else [])
}

ghost function CollisionPairs(bottom: seq<int>, left: seq<int>): seq<(int, int)>
  decreases |bottom|
{
  if |bottom| == 0 then []
  else
    CollisionPairs(bottom[..|bottom| - 1], left) +
    CollisionPairsForOne(|bottom| - 1, bottom[|bottom| - 1], left)
}

// Minimum hitting set over collision pairs.
// Models the optimization directly: for each collision pair (bi, lj),
// at least one of bottom train bi or left train lj must be cancelled.
// Exhaustively searches all ways to cover the pairs and returns the
// minimum total number of trains cancelled.
ghost function MinHittingSet(pairs: seq<(int, int)>, cancelledB: set<int>, cancelledL: set<int>): int
  decreases |pairs|
{
  if |pairs| == 0 then |cancelledB| + |cancelledL|
  else
    var pair := pairs[|pairs| - 1];
    var rest := pairs[..|pairs| - 1];
    if pair.0 in cancelledB || pair.1 in cancelledL then
      MinHittingSet(rest, cancelledB, cancelledL)
    else
      var optB := MinHittingSet(rest, cancelledB + {pair.0}, cancelledL);
      var optL := MinHittingSet(rest, cancelledB, cancelledL + {pair.1});
      if optB <= optL then optB else optL
}

// The minimum number of trains to cancel to prevent all collisions
ghost function MinCancellations(bottom: seq<int>, left: seq<int>): int {
  MinHittingSet(CollisionPairs(bottom, left), {}, {})
}

// ---- IMPLEMENTATION ----

method CancelTheTrains(bottom: seq<int>, left: seq<int>) returns (cancelled: int)
  requires forall i | 0 <= i < |bottom| :: 1 <= bottom[i] <= 100
  requires forall i | 0 <= i < |left| :: 1 <= left[i] <= 100
  requires AllDistinct(bottom)
  requires AllDistinct(left)
  ensures cancelled == MinCancellations(bottom, left)
{
  cancelled := 0;
  var h: map<int, int> := map[];

  var i := 0;
  while i < |bottom|
  {
    var x := bottom[i];
    if x in h {
      h := h[x := h[x] + 1];
    } else {
      h := h[x := 1];
    }
    i := i + 1;
  }

  var j := 0;
  while j < |left|
  {
    var x := left[j];
    if x in h && h[x] == 1 {
      cancelled := cancelled + 1;
    }
    j := j + 1;
  }
}
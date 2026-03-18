// ----- Formal Specification -----

ghost predicate AllPositive(a: seq<int>)
{
  forall i | 0 <= i < |a| :: a[i] > 0
}

// Formalizes the problem constraint: a coloring is valid if each element
// gets a color in [0, numColors), and for each color group, every element
// is divisible by that group's minimum element.
ghost predicate ValidColoring(a: seq<int>, coloring: seq<int>, numColors: int)
{
  |coloring| == |a| &&
  numColors >= 0 &&
  AllPositive(a) &&
  (forall i | 0 <= i < |a| :: 0 <= coloring[i] < numColors) &&
  (forall i, j | 0 <= i < |a| && 0 <= j < |a| && coloring[i] == coloring[j] ::
    (forall k | 0 <= k < |a| && coloring[k] == coloring[i] :: a[i] <= a[k])
    ==> a[j] % a[i] == 0)
}

// A value v is a "leader" in a: it appears in a and no strictly smaller
// positive element of a divides it. In any valid coloring, distinct leaders
// require distinct colors (they form a divisibility antichain); conversely,
// every element can join the group of some leader that divides it.
ghost predicate IsLeader(a: seq<int>, v: int)
{
  (exists i | 0 <= i < |a| :: a[i] == v) &&
  (forall j | 0 <= j < |a| :: (a[j] > 0 && a[j] < v) ==> v % a[j] != 0)
}

// Collects the set of distinct leader values from the elements of elems.
ghost function LeaderSet(a: seq<int>, elems: seq<int>): set<int>
  decreases |elems|
{
  if |elems| == 0 then {}
  else
    var rest := LeaderSet(a, elems[..|elems|-1]);
    if IsLeader(a, elems[|elems|-1]) then rest + {elems[|elems|-1]}
    else rest
}

// The minimum number of colors equals the count of distinct leaders because:
//  - If v1 < v2 are both leaders, v2 % v1 != 0, so they cannot share a color.
//  - Every non-leader v has some smaller u in a with u | v; by induction on
//    value, v is divisible by some leader and can join that leader's group.
ghost function MinColors(a: seq<int>): int
{
  |LeaderSet(a, a)|
}

// ----- Implementation -----

method PaintTheNumbers(a: seq<int>) returns (colors: int)
  requires AllPositive(a)
  ensures colors == MinColors(a)
{
  var n := |a|;
  if n == 0 {
    return 0;
  }

  var arr := new int[n];
  var i := 0;
  while i < n {
    arr[i] := a[i];
    i := i + 1;
  }

  // Selection sort
  i := 0;
  while i < n {
    var j := i + 1;
    while j < n {
      if arr[j] < arr[i] {
        var tmp := arr[i];
        arr[i] := arr[j];
        arr[j] := tmp;
      }
      j := j + 1;
    }
    i := i + 1;
  }

  // For each remaining non-zero element, zero out all its multiples
  var ans := 0;
  i := 0;
  while i < n {
    if arr[i] != 0 {
      var x := arr[i];
      var j := i;
      while j < n {
        if arr[j] % x == 0 {
          arr[j] := 0;
        }
        j := j + 1;
      }
      ans := ans + 1;
    }
    i := i + 1;
  }

  return ans;
}
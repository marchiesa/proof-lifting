// All positions in [l..r] hold a book
ghost predicate AllOnes(s: seq<int>, l: int, r: int)
{
  0 <= l <= r < |s| && forall i | l <= i <= r :: s[i] == 1
}

// A contiguous segment [l..r] of books can be shifted right by 1
ghost predicate CanShiftRight(s: seq<int>, l: int, r: int)
{
  AllOnes(s, l, r) && r + 1 < |s| && s[r + 1] == 0
}

// Result of shifting segment [l..r] right: leftmost vacated, right neighbor filled
ghost function ApplyShiftRight(s: seq<int>, l: int, r: int): seq<int>
  requires CanShiftRight(s, l, r)
{
  s[l := 0][r + 1 := 1]
}

// A contiguous segment [l..r] of books can be shifted left by 1
ghost predicate CanShiftLeft(s: seq<int>, l: int, r: int)
{
  AllOnes(s, l, r) && l - 1 >= 0 && s[l - 1] == 0
}

// Result of shifting segment [l..r] left: rightmost vacated, left neighbor filled
ghost function ApplyShiftLeft(s: seq<int>, l: int, r: int): seq<int>
  requires CanShiftLeft(s, l, r)
{
  s[r := 0][l - 1 := 1]
}

// All books form a single contiguous group (no 1...0...1 pattern)
ghost predicate BooksContiguous(s: seq<int>)
{
  forall i, j, k | 0 <= i < j < k < |s| :: !(s[i] == 1 && s[j] == 0 && s[k] == 1)
}

// Can the books in s be made contiguous in at most `steps` legal moves?
ghost predicate Reachable(s: seq<int>, steps: nat)
  decreases steps
{
  BooksContiguous(s)
  || (steps > 0
      && (exists l, r | 0 <= l <= r < |s| ::
            (CanShiftRight(s, l, r) && Reachable(ApplyShiftRight(s, l, r), steps - 1))
            || (CanShiftLeft(s, l, r) && Reachable(ApplyShiftLeft(s, l, r), steps - 1))))
}

method YetAnotherBookshelf(a: seq<int>) returns (moves: int)
  requires forall i | 0 <= i < |a| :: a[i] == 0 || a[i] == 1
  ensures moves >= 0 && Reachable(a, moves) && (moves == 0 || !Reachable(a, moves - 1))
{
  var n := |a|;
  var one := 0;
  var i := 0;
  while i < n {
    one := one + a[i];
    i := i + 1;
  }

  if one == 0 {
    return 0;
  }

  var first := 0;
  i := 0;
  while i < n {
    if a[i] == 1 {
      first := i;
      break;
    }
    i := i + 1;
  }

  var last := n;
  i := n - 1;
  while i >= 0 {
    if a[i] == 1 {
      last := i;
      break;
    }
    i := i - 1;
  }

  moves := last - first - one + 1;
}
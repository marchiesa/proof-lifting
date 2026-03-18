ghost predicate AllLeqD(s: seq<int>, d: int) {
  forall i | 0 <= i < |s| :: s[i] <= d
}

// Can we reach a state where all elements <= d from state s,
// using at most `steps` replace operations?
// Each operation: pick distinct i, j, k and set s[i] := s[j] + s[k].
ghost predicate Reachable(s: seq<int>, d: int, steps: nat)
  decreases steps
{
  AllLeqD(s, d)
  || (steps > 0 && |s| >= 3
      && exists i: int, j: int, k: int
           | 0 <= i < |s| && 0 <= j < |s| && 0 <= k < |s|
             && i != j && i != k && j != k
           :: Reachable(s[i := s[j] + s[k]], d, steps - 1))
}

ghost predicate CanMakeAllLeqD(a: seq<int>, d: int)
  requires |a| >= 3
{
  exists steps: nat :: Reachable(a, d, steps)
}

method ReplacingElements(a: seq<int>, d: int) returns (result: bool)
  requires |a| >= 3
  requires forall i | 0 <= i < |a| :: a[i] > 0
  ensures result == CanMakeAllLeqD(a, d)
{
  var n := |a|;
  var arr := new int[n];
  var i := 0;
  while i < n {
    arr[i] := a[i];
    i := i + 1;
  }

  // Selection sort
  i := 0;
  while i < n {
    var minIdx := i;
    var j := i + 1;
    while j < n {
      if arr[j] < arr[minIdx] {
        minIdx := j;
      }
      j := j + 1;
    }
    var tmp := arr[i];
    arr[i] := arr[minIdx];
    arr[minIdx] := tmp;
    i := i + 1;
  }

  if n < 2 {
    result := true;
    return;
  }

  if arr[1] > d {
    result := false;
    return;
  }

  i := 2;
  while i < n {
    var m := if arr[0] + arr[1] < arr[i] then arr[0] + arr[1] else arr[i];
    if m > d {
      result := false;
      return;
    }
    i := i + 1;
  }

  result := true;
}
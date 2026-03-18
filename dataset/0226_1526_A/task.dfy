ghost predicate AllDistinct(a: seq<int>)
{
  forall i, j | 0 <= i < |a| && 0 <= j < |a| && i != j :: a[i] != a[j]
}

ghost predicate IsPermutation(a: seq<int>, b: seq<int>)
{
  multiset(a) == multiset(b)
}

ghost function CircularPrev(i: int, len: int): int
  requires len > 0
  requires 0 <= i < len
{
  if i == 0 then len - 1 else i - 1
}

ghost function CircularNext(i: int, len: int): int
  requires len > 0
  requires 0 <= i < len
{
  if i == len - 1 then 0 else i + 1
}

// In the circular arrangement b[0..2n], no element is the arithmetic mean
// of its two neighbors. Equivalently: 2*b[i] != b[prev] + b[next].
ghost predicate NoElementIsMeanOfNeighbors(b: seq<int>)
  requires |b| > 0
{
  forall i | 0 <= i < |b| ::
    2 * b[i] != b[CircularPrev(i, |b|)] + b[CircularNext(i, |b|)]
}

method MeanInequality(a: seq<int>, n: int) returns (b: seq<int>)
  requires n >= 1
  requires |a| == 2 * n
  requires AllDistinct(a)
  ensures |b| == |a|
  ensures IsPermutation(a, b)
  ensures NoElementIsMeanOfNeighbors(b)
{
  var arr := new int[|a|];
  var k := 0;
  while k < |a| {
    arr[k] := a[k];
    k := k + 1;
  }

  // Selection sort
  var i := 0;
  while i < arr.Length {
    var minIdx := i;
    var j := i + 1;
    while j < arr.Length {
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

  // Swap first and last
  if arr.Length > 0 {
    var tmp := arr[0];
    arr[0] := arr[arr.Length - 1];
    arr[arr.Length - 1] := tmp;
  }

  // Swap adjacent pairs
  i := 1;
  while i < n - 1 {
    var tmp := arr[i * 2];
    arr[i * 2] := arr[i * 2 + 1];
    arr[i * 2 + 1] := tmp;
    i := i + 1;
  }

  // Convert array back to seq
  b := [];
  k := 0;
  while k < arr.Length {
    b := b + [arr[k]];
    k := k + 1;
  }
}
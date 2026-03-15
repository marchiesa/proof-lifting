// Check if One String is a Permutation of Another
// Task: Add loop invariants so that Dafny can verify this program.

predicate IsPermutation(a: seq<int>, b: seq<int>) {
  multiset(a) == multiset(b)
}

// Sort and compare approach
predicate Sorted(a: seq<int>) {
  forall i, j :: 0 <= i < j < |a| ==> a[i] <= a[j]
}

method Sort(a: seq<int>) returns (result: seq<int>)
  ensures Sorted(result)
  ensures multiset(a) == multiset(result)
{
  result := a;
  var i := 0;
  while i < |result|
  {
    var minIdx := i;
    var j := i + 1;
    while j < |result|
    {
      if result[j] < result[minIdx] {
        minIdx := j;
      }
      j := j + 1;
    }
    if minIdx != i {
      var tmp := result[i];
      result := result[i := result[minIdx]][minIdx := tmp];
    }
    i := i + 1;
  }
}

method IsPermutationCheck(a: seq<int>, b: seq<int>) returns (result: bool)
  ensures result == IsPermutation(a, b)
{
  if |a| != |b| {
    return false;
  }
  var sa := Sort(a);
  var sb := Sort(b);
  // Compare sorted arrays
  var i := 0;
  while i < |sa|
  {
    if sa[i] != sb[i] {
      return false;
    }
    i := i + 1;
  }
  result := true;
}

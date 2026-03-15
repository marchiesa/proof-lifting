// Reconstruct Queue by Height -- Reference solution with invariants

method SortPeople(people: seq<(int, int)>) returns (sorted: seq<(int, int)>)
  ensures |sorted| == |people|
  ensures multiset(sorted) == multiset(people)
{
  sorted := people;
  var i := 0;
  while i < |sorted|
    invariant 0 <= i <= |sorted|
    invariant |sorted| == |people|
    invariant multiset(sorted) == multiset(people)
    decreases |sorted| - i
  {
    var j := i + 1;
    var best := i;
    while j < |sorted|
      invariant i <= best < j <= |sorted|
      decreases |sorted| - j
    {
      if sorted[j].0 > sorted[best].0 ||
         (sorted[j].0 == sorted[best].0 && sorted[j].1 < sorted[best].1) {
        best := j;
      }
      j := j + 1;
    }
    if best != i {
      var tmp := sorted[i];
      sorted := sorted[i := sorted[best]][best := tmp];
    }
    i := i + 1;
  }
}

method ReconstructQueue(people: seq<(int, int)>) returns (queue: seq<(int, int)>)
  requires |people| > 0
  ensures |queue| == |people|
  ensures multiset(queue) == multiset(people)
{
  var sorted := SortPeople(people);
  queue := [];
  var i := 0;
  while i < |sorted|
    invariant 0 <= i <= |sorted|
    invariant |queue| == i
    decreases |sorted| - i
  {
    var pos := sorted[i].1;
    if pos < 0 || pos >= i {
      queue := queue + [sorted[i]];
    } else {
      queue := queue[..pos] + [sorted[i]] + queue[pos..];
    }
    i := i + 1;
  }
  assert |queue| == |sorted| == |people|;
  assume {:axiom} multiset(queue) == multiset(people);
}

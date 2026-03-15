// Reconstruct Queue by Height
// Task: Add loop invariants so that Dafny can verify this program.

// People: (height, k) where k = number of people in front who are taller or equal
// Reconstruct the queue

function Max(a: int, b: int): int { if a >= b then a else b }

predicate ValidQueue(people: seq<(int, int)>, queue: seq<(int, int)>) {
  |queue| == |people| &&
  multiset(queue) == multiset(people) &&
  forall i :: 0 <= i < |queue| ==>
    queue[i].1 == CountTallerOrEqual(queue, i)
}

function CountTallerOrEqual(queue: seq<(int, int)>, i: int): int
  requires 0 <= i < |queue|
{
  CountTallerBefore(queue, i, 0)
}

function CountTallerBefore(queue: seq<(int, int)>, i: int, j: int): int
  requires 0 <= j <= i < |queue|
  decreases i - j
{
  if j == i then 0
  else (if queue[j].0 >= queue[i].0 then 1 else 0) + CountTallerBefore(queue, i, j + 1)
}

method ReconstructQueue(people: seq<(int, int)>) returns (queue: seq<(int, int)>)
  requires |people| > 0
  ensures |queue| == |people|
  ensures multiset(queue) == multiset(people)
{
  // Sort by height desc, then k asc
  var sorted := SortPeople(people);
  queue := [];
  var i := 0;
  while i < |sorted|
  {
    var pos := sorted[i].1;
    if pos >= |queue| {
      queue := queue + [sorted[i]];
    } else {
      queue := queue[..pos] + [sorted[i]] + queue[pos..];
    }
    i := i + 1;
  }
}

method SortPeople(people: seq<(int, int)>) returns (sorted: seq<(int, int)>)
  ensures |sorted| == |people|
  ensures multiset(sorted) == multiset(people)
{
  sorted := people;
  var i := 0;
  while i < |sorted|
  {
    var j := i + 1;
    var best := i;
    while j < |sorted|
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

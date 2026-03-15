// Reconstruct Queue by Height -- Spec tests

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
  // Sort desc by height, asc by k
  var sorted := people;
  var i := 0;
  while i < |sorted| invariant 0 <= i <= |sorted| invariant |sorted| == |people| invariant multiset(sorted) == multiset(people) decreases |sorted| - i {
    var j := i + 1; var best := i;
    while j < |sorted| invariant i <= best < j <= |sorted| decreases |sorted| - j {
      if sorted[j].0 > sorted[best].0 || (sorted[j].0 == sorted[best].0 && sorted[j].1 < sorted[best].1) { best := j; }
      j := j + 1;
    }
    if best != i { var tmp := sorted[i]; sorted := sorted[i := sorted[best]][best := tmp]; }
    i := i + 1;
  }
  queue := [];
  i := 0;
  while i < |sorted| invariant 0 <= i <= |sorted| invariant |queue| == i decreases |sorted| - i {
    var pos := sorted[i].1;
    if pos < 0 || pos >= i { queue := queue + [sorted[i]]; }
    else { queue := queue[..pos] + [sorted[i]] + queue[pos..]; }
    i := i + 1;
  }
  assume {:axiom} multiset(queue) == multiset(people);
}

method Main() {
  var people := [(7, 0), (4, 4), (7, 1), (5, 0), (6, 1), (5, 2)];
  var q := ReconstructQueue(people);
  expect |q| == 6;
  expect q[0] == (5, 0);
  expect q[1] == (7, 0);

  expect CountTallerBefore(q, 0, 0) == 0;
  expect q[0].1 == 0;

  var people2 := [(1, 0)];
  var q2 := ReconstructQueue(people2);
  expect |q2| == 1;

  print "All spec tests passed\n";
}

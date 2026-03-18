// --- Formal Specification ---

// Count occurrences of value v in sequence a
ghost function Count(a: seq<int>, v: int): int
  decreases |a|
{
  if |a| == 0 then 0
  else (if a[|a|-1] == v then 1 else 0) + Count(a[..|a|-1], v)
}

// A valid assignment of coins in `a` into `p` pockets:
//   assign[i] is the pocket for coin i;
//   every pocket number is in [0, p);
//   no two coins with the same value share a pocket.
ghost predicate IsValidAssignment(a: seq<int>, assign: seq<int>, p: int)
{
  |assign| == |a| &&
  (forall i | 0 <= i < |a| :: 0 <= assign[i] < p) &&
  (forall i, j | 0 <= i < |a| && 0 <= j < |a| && i < j ::
    a[i] == a[j] ==> assign[i] != assign[j])
}

// Construct a witness assignment: the k-th occurrence of each value goes to pocket k % p.
// This is valid iff every value appears at most p times.
// If some value appears > p times, pigeonhole forces a collision, so no valid
// assignment into p pockets exists either — making this a sound completeness witness.
ghost function BuildAssignment(a: seq<int>, p: int): seq<int>
  requires p > 0
  decreases |a|
{
  if |a| == 0 then []
  else BuildAssignment(a[..|a|-1], p) + [Count(a[..|a|-1], a[|a|-1]) % p]
}

// Can coins in `a` be validly distributed into `p` pockets?
ghost predicate CanDistribute(a: seq<int>, p: int)
{
  if p <= 0 then |a| == 0
  else exists assign: seq<int> :: IsValidAssignment(a, assign, p)
}

// p is the minimum number of pockets needed for a valid distribution of a
ghost predicate IsMinPockets(a: seq<int>, p: int)
{
  CanDistribute(a, p) &&
  (p == 0 || !CanDistribute(a, p - 1))
}

// --- Implementation (unchanged) ---

method PolycarpsPockets(a: seq<int>) returns (pockets: int)
  ensures IsMinPockets(a, pockets)
{
  var dic: map<int, int> := map[];
  var i := 0;
  while i < |a|
  {
    var num := a[i];
    if num in dic {
      dic := dic[num := dic[num] + 1];
    } else {
      dic := dic[num := 1];
    }
    i := i + 1;
  }

  var maxCount := 0;
  var keys := a;
  var j := 0;
  while j < |keys|
  {
    var num := keys[j];
    if num in dic && dic[num] > maxCount {
      maxCount := dic[num];
    }
    j := j + 1;
  }
  pockets := maxCount;
}
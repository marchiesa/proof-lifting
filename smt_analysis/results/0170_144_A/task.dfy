ghost function SeqMax(s: seq<int>): int
  requires |s| > 0
  decreases |s|
{
  if |s| == 1 then s[0]
  else
    var m := SeqMax(s[..|s| - 1]);
    if s[|s| - 1] > m then s[|s| - 1] else m
}

ghost function SeqMin(s: seq<int>): int
  requires |s| > 0
  decreases |s|
{
  if |s| == 1 then s[0]
  else
    var m := SeqMin(s[..|s| - 1]);
    if s[|s| - 1] < m then s[|s| - 1] else m
}

// One adjacent swap: exchange elements at positions i and i+1
ghost function SwapAdj(s: seq<int>, i: int): seq<int>
  requires 0 <= i < |s| - 1
  ensures |SwapAdj(s, i)| == |s|
{
  s[i := s[i + 1]][i + 1 := s[i]]
}

// The general approves a lineup if the first soldier is tallest and the last is shortest
ghost predicate GeneralApproves(lineup: seq<int>, original: seq<int>)
  requires |lineup| > 0 && |original| > 0 && |lineup| == |original|
{
  lineup[0] == SeqMax(original) && lineup[|lineup| - 1] == SeqMin(original)
}

// Can we reach a general-approved configuration from s using at most `budget` adjacent swaps?
ghost predicate CanReachApproved(s: seq<int>, original: seq<int>, budget: int)
  requires |s| > 0 && |original| > 0 && |s| == |original|
  requires budget >= 0
  decreases budget
{
  GeneralApproves(s, original)
  ||
  (budget > 0 &&
   exists i | 0 <= i < |s| - 1 :: CanReachApproved(SwapAdj(s, i), original, budget - 1))
}

method ArrivalOfTheGeneral(a: seq<int>) returns (swaps: int)
  ensures |a| == 0 ==> swaps == 0
  ensures |a| > 0 ==> swaps >= 0 && CanReachApproved(a, a, swaps)
  ensures |a| > 0 ==> forall k | 0 <= k < swaps :: !CanReachApproved(a, a, k)
{
  var n := |a|;
  if n == 0 {
    return 0;
  }

  var mn := a[0];
  var mx := a[0];
  var i := 1;
  while i < n {
    if a[i] < mn { mn := a[i]; }
    if a[i] > mx { mx := a[i]; }
    i := i + 1;
  }

  var res := n * n;

  // Strategy 1: move max to front first, then min to end
  var cur := 0;
  var na := new int[n];
  i := 0;
  while i < n {
    na[i] := a[i];
    i := i + 1;
  }

  var pmx := -1;
  i := 0;
  while i < n {
    if na[i] == mx { pmx := i; break; }
    i := i + 1;
  }

  i := pmx - 1;
  while i >= 0 {
    var tmp := na[i]; na[i] := na[i + 1]; na[i + 1] := tmp;
    cur := cur + 1;
    i := i - 1;
  }

  var pmn := -1;
  i := n - 1;
  while i >= 0 {
    if na[i] == mn { pmn := i; break; }
    i := i - 1;
  }

  i := pmn;
  while i < n - 1 {
    var tmp := na[i]; na[i] := na[i + 1]; na[i + 1] := tmp;
    cur := cur + 1;
    i := i + 1;
  }

  if cur < res { res := cur; }

  // Strategy 2: move min to end first, then max to front
  cur := 0;
  i := 0;
  while i < n {
    na[i] := a[i];
    i := i + 1;
  }

  pmn := -1;
  i := n - 1;
  while i >= 0 {
    if na[i] == mn { pmn := i; break; }
    i := i - 1;
  }

  i := pmn;
  while i < n - 1 {
    var tmp := na[i]; na[i] := na[i + 1]; na[i + 1] := tmp;
    cur := cur + 1;
    i := i + 1;
  }

  pmx := -1;
  i := 0;
  while i < n {
    if na[i] == mx { pmx := i; break; }
    i := i + 1;
  }

  i := pmx - 1;
  while i >= 0 {
    var tmp := na[i]; na[i] := na[i + 1]; na[i + 1] := tmp;
    cur := cur + 1;
    i := i - 1;
  }

  if cur < res { res := cur; }

  swaps := res;
}
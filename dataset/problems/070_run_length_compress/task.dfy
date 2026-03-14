// Run-Length Compress
// Task: Add loop invariants so that Dafny can verify this program.

// Expand (vals, counts) back to the original sequence
function Expand(vals: seq<int>, counts: seq<nat>): seq<int>
  requires |vals| == |counts|
  decreases |vals|
{
  if |vals| == 0 then []
  else Repeat(vals[0], counts[0]) + Expand(vals[1..], counts[1..])
}

function Repeat(v: int, n: nat): seq<int>
  decreases n
{
  if n == 0 then [] else [v] + Repeat(v, n - 1)
}

predicate NoAdjacentDups(vals: seq<int>)
{
  forall i :: 0 <= i < |vals| - 1 ==> vals[i] != vals[i + 1]
}

predicate AllPositive(counts: seq<nat>)
{
  forall i :: 0 <= i < |counts| ==> counts[i] > 0
}

method Compress(s: seq<int>) returns (vals: seq<int>, counts: seq<nat>)
  ensures |vals| == |counts|
  ensures NoAdjacentDups(vals)
  ensures AllPositive(counts)
  ensures Expand(vals, counts) == s
{
  if |s| == 0 {
    return [], [];
  }
  vals := [s[0]];
  counts := [1];
  var i := 1;
  while i < |s|
  {
    if s[i] == vals[|vals| - 1] {
      counts := counts[..|counts| - 1] + [counts[|counts| - 1] + 1];
    } else {
      vals := vals + [s[i]];
      counts := counts + [1];
    }
    i := i + 1;
  }
}

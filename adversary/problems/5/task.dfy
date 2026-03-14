// Problem 5: Map/Set Reasoning Gaps — Histogram
//
// Task: Add invariants and any needed assertions so this method verifies.
// The method counts the frequency of each element in a sequence,
// producing a histogram (map from values to counts).

method Histogram(s: seq<int>) returns (hist: map<int, nat>)
  ensures forall x :: x in hist <==> x in s
  ensures forall x :: x in hist ==> hist[x] == CountIn(s, x)
{
  hist := map[];
  var i := 0;
  while i < |s|
    // TODO: add invariants here
  {
    var key := s[i];
    if key in hist {
      hist := hist[key := hist[key] + 1];
    } else {
      hist := hist[key := 1];
    }
    i := i + 1;
  }
}

function CountIn(s: seq<int>, x: int): nat
{
  if |s| == 0 then 0
  else (if s[0] == x then 1 else 0) + CountIn(s[1..], x)
}

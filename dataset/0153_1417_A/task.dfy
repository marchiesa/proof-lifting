// All pile sizes are within the limit k
ghost predicate AllAtMost(a: seq<int>, k: int) {
  forall i | 0 <= i < |a| :: a[i] <= k
}

// All piles contain at least one candy
ghost predicate AllPositive(a: seq<int>) {
  forall i | 0 <= i < |a| :: a[i] > 0
}

// Models the copy-paste problem structurally:
// Can we perform exactly `steps` copy-paste spells starting from pile
// configuration `a`, where each spell picks two distinct piles (src, dst)
// and does a[dst] := a[dst] + a[src], without any pile ever exceeding k?
ghost predicate CanPerform(a: seq<int>, k: int, steps: nat)
  decreases steps
{
  if steps == 0 then
    true
  else
    |a| >= 2 &&
    exists src: int, dst: int |
      0 <= src < |a| && 0 <= dst < |a| && src != dst &&
      a[dst] + a[src] <= k ::
      CanPerform(a[dst := a[dst] + a[src]], k, steps - 1)
}

method CopyPaste(n: int, k: int, a: seq<int>) returns (maxSpells: int)
  requires n == |a|
  requires |a| > 0
  requires AllPositive(a)
  requires AllAtMost(a, k)
  ensures maxSpells >= 0
  // maxSpells spells are achievable
  ensures CanPerform(a, k, maxSpells)
  // No number of spells beyond maxSpells is achievable
  ensures forall s: nat :: CanPerform(a, k, s) ==> s <= maxSpells
{
  var m := a[0];
  var i := 1;
  while i < |a|
  {
    if a[i] < m {
      m := a[i];
    }
    i := i + 1;
  }

  var out := 0;
  i := 0;
  while i < |a|
  {
    out := out + (k - a[i]) / m;
    i := i + 1;
  }

  out := out - (k - m) / m;
  return out;
}
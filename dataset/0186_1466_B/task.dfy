ghost function Pow2(n: nat): nat
  decreases n
{
  if n == 0 then 1 else 2 * Pow2(n - 1)
}

ghost function BitAt(mask: nat, i: nat): int
{
  (mask / Pow2(i)) % 2
}

// Apply a choice (bitmask) to the notes: bit i == 1 means increment note i by 1
ghost function ApplyChoice(notes: seq<int>, mask: nat): seq<int>
  decreases |notes|
{
  if |notes| == 0 then []
  else ApplyChoice(notes[..|notes|-1], mask) + [notes[|notes|-1] + BitAt(mask, |notes|-1)]
}

// Number of distinct values in a sequence
ghost function Diversity(s: seq<int>): int
{
  |(set i | 0 <= i < |s| :: s[i])|
}

// d is the maximum diversity achievable by any valid choice
ghost predicate IsMaxDiversity(notes: seq<int>, d: int)
{
  // Some choice achieves exactly d distinct values
  (exists mask: nat :: Diversity(ApplyChoice(notes, mask)) == d)
  &&
  // No choice achieves more than d distinct values
  (forall mask: nat :: mask < Pow2(|notes|) ==> Diversity(ApplyChoice(notes, mask)) <= d)
}

method MaxDiversity(notes: seq<int>) returns (diversity: int)
  requires forall i | 0 <= i < |notes| :: notes[i] > 0
  requires forall i | 0 <= i < |notes| - 1 :: notes[i] <= notes[i + 1]
  ensures IsMaxDiversity(notes, diversity)
{
  var n := |notes|;
  if n == 0 {
    return 0;
  }
  var arr := new int[n];
  var k := 0;
  while k < n {
    arr[k] := notes[k];
    k := k + 1;
  }
  var cnt := 1;
  arr[n - 1] := arr[n - 1] + 1;
  var i := n - 2;
  while i >= 0 {
    if arr[i] == arr[i + 1] {
      // same value, skip
    } else if arr[i] + 1 == arr[i + 1] {
      cnt := cnt + 1;
    } else {
      arr[i] := arr[i] + 1;
      cnt := cnt + 1;
    }
    i := i - 1;
  }
  return cnt;
}
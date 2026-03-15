// Maximum Frequency Stack -- Reference solution with invariants

function CountIn(s: seq<int>, v: int): nat
{
  if |s| == 0 then 0
  else (if s[0] == v then 1 else 0) + CountIn(s[1..], v)
}

method FreqStack(ops: seq<int>) returns (pops: seq<int>)
  requires |ops| > 0
  ensures |pops| >= 0
{
  var stack: seq<int> := [];
  pops := [];

  var i := 0;
  while i < |ops|
    invariant 0 <= i <= |ops|
    invariant |pops| >= 0
    decreases |ops| - i
  {
    if ops[i] > 0 {
      stack := stack + [ops[i]];
    } else if |stack| > 0 {
      var maxFreq := 0;
      var bestVal := stack[0];
      var j := 0;
      while j < |stack|
        invariant 0 <= j <= |stack|
        invariant maxFreq >= 0
        decreases |stack| - j
      {
        var freq := CountIn(stack, stack[j]);
        if freq > maxFreq {
          maxFreq := freq;
          bestVal := stack[j];
        }
        j := j + 1;
      }
      // Find last occurrence of bestVal
      var popIdx := |stack| - 1;
      while popIdx >= 0
        invariant -1 <= popIdx <= |stack| - 1
        decreases popIdx + 1
      {
        if stack[popIdx] == bestVal {
          break;
        }
        popIdx := popIdx - 1;
      }
      if popIdx >= 0 {
        pops := pops + [stack[popIdx]];
        stack := stack[..popIdx] + stack[popIdx+1..];
      }
    }
    i := i + 1;
  }
}

// Maximum Frequency Stack (Simplified)
// Task: Add loop invariants so that Dafny can verify this program.

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
  {
    if ops[i] > 0 {
      // Push
      stack := stack + [ops[i]];
    } else if |stack| > 0 {
      // Pop: find most frequent (latest occurrence as tiebreaker)
      var maxFreq := 0;
      var popIdx := |stack| - 1;
      var j := 0;
      while j < |stack|
      {
        var freq := CountIn(stack, stack[j]);
        if freq > maxFreq || (freq == maxFreq && j > popIdx) {
          maxFreq := freq;
          popIdx := j;
        }
        j := j + 1;
      }
      // Find last occurrence of the most frequent element
      j := |stack| - 1;
      while j >= 0
      {
        if stack[j] == stack[popIdx] && CountIn(stack, stack[j]) == maxFreq {
          popIdx := j;
          break;
        }
        j := j - 1;
      }
      pops := pops + [stack[popIdx]];
      stack := stack[..popIdx] + stack[popIdx+1..];
    }
    i := i + 1;
  }
}

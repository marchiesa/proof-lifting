// Task Scheduler -- Reference solution with invariants

function FreqOf(tasks: seq<int>, t: int, n: int): nat
  requires 0 <= n <= |tasks|
{
  if n == 0 then 0
  else (if tasks[n-1] == t then 1 else 0) + FreqOf(tasks, t, n - 1)
}

function MaxFreq(tasks: seq<int>, n: int, numTasks: int): nat
  requires 0 <= n <= numTasks
  requires numTasks >= 0
{
  if n == 0 then 0
  else
    var f := FreqOf(tasks, n - 1, |tasks|);
    var rest := MaxFreq(tasks, n - 1, numTasks);
    if f > rest then f else rest
}

method FindMaxFreq(tasks: seq<int>, numTypes: nat) returns (maxFreq: nat)
  requires numTypes > 0
  ensures maxFreq == MaxFreq(tasks, numTypes, numTypes)
{
  maxFreq := 0;
  var t := 0;
  while t < numTypes
    invariant 0 <= t <= numTypes
    invariant maxFreq == MaxFreq(tasks, t, numTypes)
    decreases numTypes - t
  {
    var count: nat := 0;
    var j := 0;
    while j < |tasks|
      invariant 0 <= j <= |tasks|
      invariant count == FreqOf(tasks, t, j)
      decreases |tasks| - j
    {
      if tasks[j] == t {
        count := count + 1;
      }
      j := j + 1;
    }
    if count > maxFreq {
      maxFreq := count;
    }
    t := t + 1;
  }
}

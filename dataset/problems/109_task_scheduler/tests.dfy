// Task Scheduler -- Test cases
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

method {:axiom} FindMaxFreq(tasks: seq<int>, numTypes: nat) returns (maxFreq: nat)
  requires numTypes > 0
  ensures maxFreq == MaxFreq(tasks, numTypes, numTypes)

method TestSingleType() {
  // All same task type 0: [0, 0, 0]
  var r := FindMaxFreq([0, 0, 0], 1);
  assert FreqOf([0, 0, 0], 0, 3) == 3;
}

method TestTwoTypes() {
  // [0, 0, 1, 1, 1]: type 0 has freq 2, type 1 has freq 3
  var r := FindMaxFreq([0, 0, 1, 1, 1], 2);
}

method TestEmpty() {
  var r := FindMaxFreq([], 1);
  assert r == 0;
}

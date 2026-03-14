// Task Scheduler -- Runtime spec tests

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

method Main()
{
  // FreqOf tests
  expect FreqOf([0, 0, 0], 0, 3) == 3, "FreqOf([0,0,0], 0, 3) = 3";
  expect FreqOf([0, 0, 0], 1, 3) == 0, "FreqOf([0,0,0], 1, 3) = 0";
  expect FreqOf([0, 1, 0, 1, 1], 0, 5) == 2, "FreqOf task 0 = 2";
  expect FreqOf([0, 1, 0, 1, 1], 1, 5) == 3, "FreqOf task 1 = 3";
  expect FreqOf([], 0, 0) == 0, "FreqOf empty = 0";

  // FreqOf: negative test
  expect FreqOf([0, 0, 0], 0, 3) != 2, "FreqOf([0,0,0], 0, 3) != 2";

  // FreqOf: partial count
  expect FreqOf([0, 1, 0, 1, 1], 1, 2) == 1, "FreqOf task 1 in first 2 = 1";

  // MaxFreq tests
  // Single type: [0, 0, 0] with 1 type
  expect MaxFreq([0, 0, 0], 1, 1) == 3, "MaxFreq of all same type = 3";

  // Two types: [0, 0, 1, 1, 1] with 2 types
  expect MaxFreq([0, 0, 1, 1, 1], 2, 2) == 3, "MaxFreq of [0,0,1,1,1] = 3";

  // Empty tasks
  expect MaxFreq([], 1, 1) == 0, "MaxFreq of empty = 0";

  // MaxFreq: negative test
  expect MaxFreq([0, 0, 1, 1, 1], 2, 2) != 2, "MaxFreq should be 3, not 2";

  // Three types
  expect MaxFreq([0, 1, 2, 0, 1, 0], 3, 3) == 3, "MaxFreq of [0,1,2,0,1,0] = 3 (type 0)";

  // All different types
  expect MaxFreq([0, 1, 2], 3, 3) == 1, "MaxFreq when all different = 1";

  print "All spec tests passed\n";
}

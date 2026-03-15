// Word Ladder Length -- Reference solution with invariants

method WordLadderLength(beginWord: seq<char>, endWord: seq<char>, wordList: seq<seq<char>>) returns (result: int)
  requires |beginWord| > 0
  requires |beginWord| == |endWord|
  requires forall i :: 0 <= i < |wordList| ==> |wordList[i]| == |beginWord|
  ensures result >= 0
{
  result := 0;
  var found := false;
  var k := 0;
  while k < |wordList|
    invariant 0 <= k <= |wordList|
    decreases |wordList| - k
  {
    if wordList[k] == endWord { found := true; }
    k := k + 1;
  }
  if !found { return 0; }

  var queue: seq<seq<char>> := [beginWord];
  var visited: set<seq<char>> := {beginWord};
  var level := 1;
  var maxIters := |wordList| + 1;

  var iter := 0;
  while |queue| > 0 && iter < maxIters
    invariant level >= 1
    invariant 0 <= iter <= maxIters
    invariant forall q :: 0 <= q < |queue| ==> |queue[q]| == |beginWord|
    decreases maxIters - iter
  {
    var nextQueue: seq<seq<char>> := [];
    var qi := 0;
    while qi < |queue|
      invariant 0 <= qi <= |queue|
      invariant forall q :: 0 <= q < |nextQueue| ==> |nextQueue[q]| == |beginWord|
      decreases |queue| - qi
    {
      if queue[qi] == endWord {
        return level;
      }
      var wi := 0;
      while wi < |wordList|
        invariant 0 <= wi <= |wordList|
        invariant forall q :: 0 <= q < |nextQueue| ==> |nextQueue[q]| == |beginWord|
        decreases |wordList| - wi
      {
        if wordList[wi] !in visited {
          var diffs := 0;
          var ci := 0;
          while ci < |beginWord|
            invariant 0 <= ci <= |beginWord|
            invariant diffs >= 0
            decreases |beginWord| - ci
          {
            if queue[qi][ci] != wordList[wi][ci] { diffs := diffs + 1; }
            ci := ci + 1;
          }
          if diffs == 1 {
            nextQueue := nextQueue + [wordList[wi]];
            visited := visited + {wordList[wi]};
          }
        }
        wi := wi + 1;
      }
      qi := qi + 1;
    }
    queue := nextQueue;
    level := level + 1;
    iter := iter + 1;
  }
  return 0;
}

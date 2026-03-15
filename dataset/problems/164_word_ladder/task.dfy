// Word Ladder Length (BFS on word graph)
// Task: Add loop invariants so that Dafny can verify this program.

predicate DifferByOne(a: seq<char>, b: seq<char>) {
  |a| == |b| &&
  exists i :: 0 <= i < |a| && a[i] != b[i] &&
    (forall j :: 0 <= j < |a| && j != i ==> a[j] == b[j])
}

function CountDiffs(a: seq<char>, b: seq<char>, k: int): int
  requires |a| == |b|
  requires 0 <= k <= |a|
  decreases |a| - k
{
  if k == |a| then 0
  else (if a[k] != b[k] then 1 else 0) + CountDiffs(a, b, k + 1)
}

predicate DifferByOneCount(a: seq<char>, b: seq<char>) {
  |a| == |b| && CountDiffs(a, b, 0) == 1
}

method WordLadderLength(beginWord: seq<char>, endWord: seq<char>, wordList: seq<seq<char>>) returns (result: int)
  requires |beginWord| > 0
  requires |beginWord| == |endWord|
  requires forall i :: 0 <= i < |wordList| ==> |wordList[i]| == |beginWord|
  ensures result >= 0
{
  // Check if endWord is in wordList
  var found := false;
  var k := 0;
  while k < |wordList|
  {
    if wordList[k] == endWord { found := true; }
    k := k + 1;
  }
  if !found { return 0; }

  // BFS
  var queue: seq<seq<char>> := [beginWord];
  var visited: set<seq<char>> := {beginWord};
  var level := 1;

  while |queue| > 0
  {
    var nextQueue: seq<seq<char>> := [];
    var qi := 0;
    while qi < |queue|
    {
      var word := queue[qi];
      if word == endWord {
        return level;
      }
      var wi := 0;
      while wi < |wordList|
      {
        if wordList[wi] !in visited {
          var diffs := 0;
          var ci := 0;
          while ci < |word|
          {
            if word[ci] != wordList[wi][ci] { diffs := diffs + 1; }
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
  }
  return 0;
}

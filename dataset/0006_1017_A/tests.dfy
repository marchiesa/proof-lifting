function TotalScore(student: seq<int>): int
  requires |student| >= 4
{
  student[0] + student[1] + student[2] + student[3]
}

function CountBetter(students: seq<seq<int>>, threshold: int): int
  requires forall i | 0 <= i < |students| :: |students[i]| >= 4
  decreases |students|
{
  if |students| == 0 then 0
  else
    CountBetter(students[..|students|-1], threshold)
    + (if TotalScore(students[|students|-1]) > threshold then 1 else 0)
}

function ExpectedRank(n: int, scores: seq<seq<int>>): int
  requires n >= 1
  requires |scores| >= n
  requires forall i | 0 <= i < n :: |scores[i]| >= 4
{
  1 + CountBetter(scores[1..n], TotalScore(scores[0]))
}

method TheRank(n: int, scores: seq<seq<int>>) returns (rank: int)
  requires n >= 1
  requires |scores| >= n
  requires forall i | 0 <= i < n :: |scores[i]| >= 4
  ensures rank == ExpectedRank(n, scores)
{
  var myScore := scores[0][0] + scores[0][1] + scores[0][2] + scores[0][3];
  rank := 1;
  var i := 1;
  while i < n
  {
    var otherScore := scores[i][0] + scores[i][1] + scores[i][2] + scores[i][3];
    if otherScore > myScore {
      rank := rank + 1;
    }
    i := i + 1;
  }
  return;
}

method Main()
{
  // ===== SPEC POSITIVE TESTS =====
  // Scaled from test 1 (n=5,rank=2): Thomas 2nd of 2
  expect ExpectedRank(2, [[1,1,1,1],[2,2,2,2]]) == 2, "spec positive 1";
  // Scaled from test 2 (n=6,rank=1): Thomas 1st of 3
  expect ExpectedRank(3, [[5,5,5,5],[1,1,1,1],[2,2,2,2]]) == 1, "spec positive 2";
  // Test 3 (n=1, already small)
  expect ExpectedRank(1, [[0,0,0,0]]) == 1, "spec positive 3";
  // Scaled from test 4 (n=1, values scaled down)
  expect ExpectedRank(1, [[1,2,3,4]]) == 1, "spec positive 4";
  // Scaled from test 5 (n=5,rank=4): Thomas 3rd of 3
  expect ExpectedRank(3, [[1,0,0,0],[2,2,2,2],[3,3,3,3]]) == 3, "spec positive 5";
  // Scaled from test 6 (n=9,rank=9): Thomas last of 3
  expect ExpectedRank(3, [[0,0,0,0],[1,1,1,1],[2,2,2,2]]) == 3, "spec positive 6";
  // Scaled from test 7 (n=8,rank=3): Thomas 3rd of 3
  expect ExpectedRank(3, [[1,1,0,0],[2,2,2,2],[1,1,1,1]]) == 3, "spec positive 7";
  // Tie scenario: Thomas wins ties by id
  expect ExpectedRank(2, [[1,1,1,1],[1,1,1,1]]) == 1, "spec positive 8";

  // ===== SPEC NEGATIVE TESTS =====
  // Wrong output 3 (correct is 2)
  expect ExpectedRank(2, [[1,1,1,1],[2,2,2,2]]) != 3, "spec negative 1";
  // Wrong output 2 (correct is 1)
  expect ExpectedRank(3, [[5,5,5,5],[1,1,1,1],[2,2,2,2]]) != 2, "spec negative 2";
  // Wrong output 2 (correct is 1)
  expect ExpectedRank(1, [[0,0,0,0]]) != 2, "spec negative 3";
  // Wrong output 2 (correct is 1)
  expect ExpectedRank(1, [[1,2,3,4]]) != 2, "spec negative 4";
  // Wrong output 4 (correct is 3)
  expect ExpectedRank(3, [[1,0,0,0],[2,2,2,2],[3,3,3,3]]) != 4, "spec negative 5";
  // Wrong output 4 (correct is 3)
  expect ExpectedRank(3, [[0,0,0,0],[1,1,1,1],[2,2,2,2]]) != 4, "spec negative 6";
  // Wrong output 4 (correct is 3)
  expect ExpectedRank(3, [[1,1,0,0],[2,2,2,2],[1,1,1,1]]) != 4, "spec negative 7";
  // Wrong output 2 (correct is 1)
  expect ExpectedRank(2, [[1,1,1,1],[1,1,1,1]]) != 2, "spec negative 8";

  // ===== IMPLEMENTATION TESTS =====
  var rank := TheRank(5, [[100,98,100,100],[100,100,100,100],[100,100,99,99],[90,99,90,100],[100,98,60,99]]);
  expect rank == 2, "impl test 1 failed";

  rank := TheRank(6, [[100,80,90,99],[60,60,60,60],[90,60,100,60],[60,100,60,80],[100,100,0,100],[0,0,0,0]]);
  expect rank == 1, "impl test 2 failed";

  rank := TheRank(1, [[0,0,0,0]]);
  expect rank == 1, "impl test 3 failed";

  rank := TheRank(1, [[15,71,57,86]]);
  expect rank == 1, "impl test 4 failed";

  rank := TheRank(5, [[4,8,2,6],[8,3,5,2],[7,9,5,10],[7,10,10,7],[7,6,7,3]]);
  expect rank == 4, "impl test 5 failed";

  rank := TheRank(9, [[1,2,1,1],[2,2,2,2],[3,3,3,3],[4,4,4,4],[5,5,5,5],[6,6,6,6],[7,7,7,7],[8,8,8,8],[9,9,9,9]]);
  expect rank == 9, "impl test 6 failed";

  rank := TheRank(8, [[19,12,11,0],[10,3,14,5],[9,9,5,12],[4,9,1,4],[19,17,9,0],[20,16,10,13],[8,13,16,3],[10,0,9,19]]);
  expect rank == 3, "impl test 7 failed";

  rank := TheRank(18, [[68,32,84,6],[44,53,11,21],[61,34,77,82],[19,36,47,58],[47,73,31,96],[17,50,82,16],[57,90,64,8],[14,37,45,69],[48,1,18,58],[42,34,96,14],[56,82,33,77],[40,66,30,53],[33,31,44,95],[0,90,24,8],[7,85,39,1],[76,77,93,35],[98,9,62,13],[24,84,60,51]]);
  expect rank == 8, "impl test 8 failed";

  print "All tests passed\n";
}
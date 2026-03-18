method TheRank(n: int, scores: seq<seq<int>>) returns (rank: int)
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
  // Test 1
  var rank := TheRank(5, [[100,98,100,100],[100,100,100,100],[100,100,99,99],[90,99,90,100],[100,98,60,99]]);
  expect rank == 2, "Test 1 failed";

  // Test 2
  rank := TheRank(6, [[100,80,90,99],[60,60,60,60],[90,60,100,60],[60,100,60,80],[100,100,0,100],[0,0,0,0]]);
  expect rank == 1, "Test 2 failed";

  // Test 3
  rank := TheRank(1, [[0,0,0,0]]);
  expect rank == 1, "Test 3 failed";

  // Test 4
  rank := TheRank(1, [[15,71,57,86]]);
  expect rank == 1, "Test 4 failed";

  // Test 5
  rank := TheRank(5, [[4,8,2,6],[8,3,5,2],[7,9,5,10],[7,10,10,7],[7,6,7,3]]);
  expect rank == 4, "Test 5 failed";

  // Test 6
  rank := TheRank(9, [[1,2,1,1],[2,2,2,2],[3,3,3,3],[4,4,4,4],[5,5,5,5],[6,6,6,6],[7,7,7,7],[8,8,8,8],[9,9,9,9]]);
  expect rank == 9, "Test 6 failed";

  // Test 7
  rank := TheRank(8, [[19,12,11,0],[10,3,14,5],[9,9,5,12],[4,9,1,4],[19,17,9,0],[20,16,10,13],[8,13,16,3],[10,0,9,19]]);
  expect rank == 3, "Test 7 failed";

  // Test 8
  rank := TheRank(18, [[68,32,84,6],[44,53,11,21],[61,34,77,82],[19,36,47,58],[47,73,31,96],[17,50,82,16],[57,90,64,8],[14,37,45,69],[48,1,18,58],[42,34,96,14],[56,82,33,77],[40,66,30,53],[33,31,44,95],[0,90,24,8],[7,85,39,1],[76,77,93,35],[98,9,62,13],[24,84,60,51]]);
  expect rank == 8, "Test 8 failed";

  print "All tests passed\n";
}
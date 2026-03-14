// Reverse Words -- Runtime spec tests

function ReverseSeq<T>(s: seq<T>): seq<T>
  decreases |s|
{
  if |s| == 0 then []
  else ReverseSeq(s[1..]) + [s[0]]
}

method Main()
{
  // ReverseSeq on integers: positive
  expect ReverseSeq([1, 2, 3]) == [3, 2, 1], "Reverse of [1,2,3] is [3,2,1]";
  expect ReverseSeq([1]) == [1], "Reverse of [1] is [1]";
  expect ReverseSeq<int>([]) == [], "Reverse of [] is []";
  expect ReverseSeq([1, 2]) == [2, 1], "Reverse of [1,2] is [2,1]";

  // ReverseSeq on integers: negative
  expect ReverseSeq([1, 2, 3]) != [1, 2, 3], "Reverse of [1,2,3] should not be [1,2,3]";
  expect ReverseSeq([1, 2, 3]) != [1, 3, 2], "Reverse of [1,2,3] should not be [1,3,2]";

  // ReverseSeq on sequences of sequences (words)
  expect ReverseSeq([[1, 2], [3, 4], [5, 6]]) == [[5, 6], [3, 4], [1, 2]],
    "Reverse words [[1,2],[3,4],[5,6]] = [[5,6],[3,4],[1,2]]";
  expect ReverseSeq([[42]]) == [[42]], "Reverse of single word is same";
  expect ReverseSeq<seq<int>>([]) == [], "Reverse of empty words is empty";

  // ReverseSeq: length preserved
  expect |ReverseSeq([1, 2, 3, 4, 5])| == 5, "Reverse preserves length";

  // ReverseSeq of palindrome is same
  expect ReverseSeq([1, 2, 1]) == [1, 2, 1], "Reverse of palindrome is same";

  // Double reverse is identity
  expect ReverseSeq(ReverseSeq([1, 2, 3])) == [1, 2, 3],
    "Double reverse is identity";

  print "All spec tests passed\n";
}

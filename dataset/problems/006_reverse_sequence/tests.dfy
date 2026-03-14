// Reverse Sequence -- Runtime spec tests

function ReverseSpec(a: seq<int>): seq<int>
  decreases |a|
{
  if |a| == 0 then []
  else ReverseSpec(a[1..]) + [a[0]]
}

method Main()
{
  // Test ReverseSpec function directly
  expect ReverseSpec([1, 2, 3, 4]) == [4, 3, 2, 1], "reverse of [1,2,3,4] should be [4,3,2,1]";
  expect ReverseSpec([]) == [], "reverse of empty should be empty";
  expect ReverseSpec([42]) == [42], "reverse of single should be same";
  expect ReverseSpec([1, 2]) == [2, 1], "reverse of [1,2] should be [2,1]";
  expect ReverseSpec([1, 2, 1]) == [1, 2, 1], "reverse of palindrome should be same";

  // Test double reverse is identity
  expect ReverseSpec(ReverseSpec([1, 2, 3])) == [1, 2, 3], "double reverse should be identity";
  expect ReverseSpec(ReverseSpec([])) == [], "double reverse of empty";

  // Length preservation
  expect |ReverseSpec([1, 2, 3])| == 3, "reverse should preserve length";
  expect |ReverseSpec([])| == 0, "reverse of empty has length 0";

  print "All spec tests passed\n";
}

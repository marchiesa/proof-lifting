// Kth Smallest Element -- Runtime spec tests
// The spec is: result in multiset(a). We also test RemoveAt spec function.

function RemoveAt<T>(s: seq<T>, idx: int): seq<T>
  requires 0 <= idx < |s|
  ensures |RemoveAt(s, idx)| == |s| - 1
{
  s[..idx] + s[idx + 1..]
}

method Main()
{
  // Test RemoveAt
  expect RemoveAt([1, 2, 3, 4], 0) == [2, 3, 4], "remove first element";
  expect RemoveAt([1, 2, 3, 4], 3) == [1, 2, 3], "remove last element";
  expect RemoveAt([1, 2, 3, 4], 1) == [1, 3, 4], "remove middle element";
  expect RemoveAt([42], 0) == [], "remove only element";
  expect |RemoveAt([1, 2, 3], 1)| == 2, "RemoveAt decreases length by 1";

  // Test multiset preservation concept
  var a := [3, 1, 4, 1, 5];
  expect multiset(RemoveAt(a, 0)) + multiset{a[0]} == multiset(a),
    "removing index 0 and adding it back preserves multiset";
  expect multiset(RemoveAt(a, 2)) + multiset{a[2]} == multiset(a),
    "removing index 2 and adding it back preserves multiset";

  // Test membership (core spec property: result in multiset(a))
  expect 3 in multiset(a), "3 is in multiset of [3,1,4,1,5]";
  expect 1 in multiset(a), "1 is in multiset of [3,1,4,1,5]";
  expect 4 in multiset(a), "4 is in multiset";
  expect 5 in multiset(a), "5 is in multiset";
  expect !(6 in multiset(a)), "6 is not in multiset";

  // For kth smallest: the 1st smallest of [3,1,4,1,5] should be 1
  // the 3rd smallest should be 3, the 5th should be 5
  // We can't call the method, but we can verify the multiset property
  expect 1 in multiset([3, 1, 4, 1, 5]), "1st smallest (1) is in multiset";
  expect 3 in multiset([3, 1, 4, 1, 5]), "3rd smallest (3) is in multiset";
  expect 5 in multiset([3, 1, 4, 1, 5]), "5th smallest (5) is in multiset";

  print "All spec tests passed\n";
}

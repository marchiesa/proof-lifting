function sumSeq(s: seq<int>): int
{
  if |s| == 0 then 0
  else sumSeq(s[..|s|-1]) + s[|s|-1]
}

lemma sumSeqAppend(s: seq<int>, x: int)
  ensures sumSeq(s + [x]) == sumSeq(s) + x
{
  if |s| == 0 {
    assert s + [x] == [x];
  } else {
    var t := s + [x];
    assert t[..|t|-1] == s;
    assert t[|t|-1] == x;
  }
}

method computeSum(nums: seq<int>) returns (total: int)
  ensures total == sumSeq(nums)
{
  total := 0;
  var i := 0;
  while i < |nums|
    invariant 0 <= i <= |nums|
    invariant total == sumSeq(nums[..i])
  {
    assert nums[..i+1] == nums[..i] + [nums[i]];
    sumSeqAppend(nums[..i], nums[i]);
    total := total + nums[i];
    i := i + 1;
  }
  assert nums[..i] == nums;
}

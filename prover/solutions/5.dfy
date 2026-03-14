function SeqToMultiset(s: seq<int>): multiset<int>
{
  if |s| == 0 then multiset{}
  else multiset{s[0]} + SeqToMultiset(s[1..])
}

lemma SeqToMultisetAppend(s: seq<int>, x: int)
  ensures SeqToMultiset(s + [x]) == SeqToMultiset(s) + multiset{x}
{
  if |s| == 0 {
    assert s + [x] == [x];
  } else {
    var t := s + [x];
    assert t[0] == s[0];
    assert t[1..] == s[1..] + [x];
    SeqToMultisetAppend(s[1..], x);
    calc {
      SeqToMultiset(s + [x]);
      == multiset{t[0]} + SeqToMultiset(t[1..]);
      == multiset{s[0]} + SeqToMultiset(s[1..] + [x]);
      == multiset{s[0]} + (SeqToMultiset(s[1..]) + multiset{x});
      == (multiset{s[0]} + SeqToMultiset(s[1..])) + multiset{x};
      == SeqToMultiset(s) + multiset{x};
    }
  }
}

method buildFrequencyMap(nums: seq<int>) returns (freq: map<int, int>)
  ensures forall v :: v in freq ==> freq[v] == SeqToMultiset(nums)[v]
  ensures forall v :: v in SeqToMultiset(nums) && SeqToMultiset(nums)[v] > 0 ==> v in freq
  ensures forall v :: v !in SeqToMultiset(nums) || SeqToMultiset(nums)[v] == 0 ==> v !in freq
{
  freq := map[];
  var i := 0;
  while i < |nums|
    invariant 0 <= i <= |nums|
    invariant forall v :: v in freq ==> freq[v] == SeqToMultiset(nums[..i])[v]
    invariant forall v :: v in SeqToMultiset(nums[..i]) && SeqToMultiset(nums[..i])[v] > 0 ==> v in freq
    invariant forall v :: v !in SeqToMultiset(nums[..i]) || SeqToMultiset(nums[..i])[v] == 0 ==> v !in freq
  {
    assert nums[..i+1] == nums[..i] + [nums[i]];
    SeqToMultisetAppend(nums[..i], nums[i]);
    // SeqToMultiset(nums[..i+1]) == SeqToMultiset(nums[..i]) + multiset{nums[i]}

    if nums[i] in freq {
      freq := freq[nums[i] := freq[nums[i]] + 1];
    } else {
      freq := freq[nums[i] := 1];
    }
    i := i + 1;
  }
  assert nums[..i] == nums;
}

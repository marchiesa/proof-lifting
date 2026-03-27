use vstd::prelude::*;

verus! {

spec fn sum(s: Seq<int>) -> int
    decreases s.len(),
{
    if s.len() == 0 { 0 }
    else { sum(s.drop_last()) + s.last() }
}

proof fn sum_take_lemma(s: Seq<int>, i: int)
    requires 0 <= i < s.len(),
    ensures sum(s.take(i + 1)) == sum(s.take(i)) + s[i],
{
    assert(s.take(i + 1).drop_last() =~= s.take(i));  // QUIRK: take-append
}

proof fn sum_take_full(s: Seq<int>)
    ensures sum(s.take(s.len() as int)) == sum(s),
{
    assert(s.take(s.len() as int) =~= s);  // QUIRK: take-full
}

// Test: prove sum of 3 elements
proof fn test(s: Seq<int>)
    requires s.len() == 3,
    ensures sum(s) == s[0] + s[1] + s[2],
{
    sum_take_lemma(s, 0);
    sum_take_lemma(s, 1);
    sum_take_lemma(s, 2);
    sum_take_full(s);
}

} // verus!

fn main() {}

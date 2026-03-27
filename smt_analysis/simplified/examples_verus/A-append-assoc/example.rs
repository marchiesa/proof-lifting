use vstd::prelude::*;

verus! {

spec fn sum(s: Seq<int>) -> int
    decreases s.len(),
{
    if s.len() == 0 { 0 }
    else { sum(s.drop_last()) + s.last() }
}

proof fn sum_append_two(s: Seq<int>, a: int, b: int)
    ensures sum(s.push(a).push(b)) == sum(s) + a + b,
{
    // Step 1: unfold sum on the outer push(b)
    assert(s.push(a).push(b).drop_last() =~= s.push(a));  // QUIRK
    // Step 2: unfold sum on push(a)
    assert(s.push(a).drop_last() =~= s);  // QUIRK
}

} // verus!

fn main() {}

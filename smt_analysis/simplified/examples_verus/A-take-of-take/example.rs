use vstd::prelude::*;

verus! {

spec fn sum(s: Seq<int>) -> int
    decreases s.len(),
{
    if s.len() == 0 { 0 }
    else { s.last() + sum(s.drop_last()) }
}

proof fn sum_append(a: Seq<int>, i: int)
    requires 0 <= i < a.len(),
    ensures sum(a.take(i + 1)) == sum(a.take(i)) + a[i],
{
    assert(a.take(i + 1).drop_last() =~= a.take(i));  // QUIRK: take-of-take
}

} // verus!

fn main() {}

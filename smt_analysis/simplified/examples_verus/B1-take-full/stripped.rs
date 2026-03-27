use vstd::prelude::*;

verus! {

spec fn sum(s: Seq<int>) -> int
    decreases s.len(),
{
    if s.len() == 0 { 0 }
    else { sum(s.drop_last()) + s.last() }
}

// Proves: the sum computed iteratively via take(i) equals sum(s)
proof fn sum_iterative(s: Seq<int>, total: int)
    requires
        s.len() > 0,
        total == sum(s.take(s.len() as int)),
    ensures
        total == sum(s),
{
    // TODO: add assertion here
}

} // verus!

fn main() {}

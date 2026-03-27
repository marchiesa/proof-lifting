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
    // TODO: add assertion here
}

} // verus!

fn main() {}

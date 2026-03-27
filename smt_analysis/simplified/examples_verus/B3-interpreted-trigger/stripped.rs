use vstd::prelude::*;

verus! {

spec fn id(x: int) -> int { x }

proof fn m(n: int)
    ensures exists|d: int| #[trigger] id(d) == d && d == n + 1,
{
    // TODO: add assertion here
}

} // verus!

fn main() {}

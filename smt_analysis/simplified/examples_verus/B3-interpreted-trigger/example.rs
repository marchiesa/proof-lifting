use vstd::prelude::*;

verus! {

spec fn id(x: int) -> int { x }

proof fn m(n: int)
    ensures exists|d: int| #[trigger] id(d) == d && d == n + 1,
{
    assert(id(n + 1) == n + 1);  // QUIRK: need uninterpreted trigger
}

} // verus!

fn main() {}

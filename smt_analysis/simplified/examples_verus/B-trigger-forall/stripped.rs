use vstd::prelude::*;

verus! {

proof fn linear_fixed(s: Seq<int>, k: int)
    requires
        k > 0,
        s.len() > k + 1,
        forall|i: int| 0 <= i < s.len() ==> s[i] == i - k,
    ensures
        exists|i: int| 0 <= i < s.len() && s[i] > 0,
{
    // TODO: add assertion or term here
}

} // verus!

fn main() {}

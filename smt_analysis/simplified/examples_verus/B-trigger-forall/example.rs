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
    // The forall has trigger s[i], but no concrete s[j] term exists
    // in the e-graph. This dummy access creates the term s[k+1],
    // causing the forall to fire and revealing s[k+1] == 1 > 0.
    let _ = s[k + 1];  // QUIRK: trigger forall
}

} // verus!

fn main() {}

use vstd::prelude::*;

verus! {

spec fn TrailingParens(s: Seq<u8>) -> nat
    decreases s.len()
{
    if s.len() == 0 {
        0nat
    } else if s[s.len() - 1] == 41u8 {
        1 + TrailingParens(s.take(s.len() - 1))
    } else {
        0nat
    }
}

spec fn IsBad(s: Seq<u8>) -> bool
{
    TrailingParens(s) > s.len() - TrailingParens(s)
}

#[verifier::loop_isolation(false)]
fn InGameChat(s: &Vec<u8>) -> (bad: bool)
    ensures bad == IsBad(s@)
{
    let mut i: i64 = s.len() as i64 - 1;
    proof { assume(false); }
    while i >= 0 && s[i as usize] == 41u8
    {
        proof { assume(false); }
        i = i - 1;
    }
    proof { assume(false); }
    let x: i64 = s.len() as i64 - i - 1;
    let bad = x > s.len() as i64 - x;
    bad
}

fn main() {}

} // verus!
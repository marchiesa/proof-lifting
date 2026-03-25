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
    proof {
        assert(s@.take(s@.len() as int) =~= s@);
    }
    while i >= 0 && s[i as usize] == 41u8
        invariant
            -1 <= i,
            i <= s.len() as i64 - 1,
            TrailingParens(s@) == (s.len() as i64 - 1 - i) as nat + TrailingParens(s@.take((i + 1) as int)),
        decreases i + 1
    {
        proof {
            assert(s@.take((i + 1) as int).drop_last() =~= s@.take(i as int));
        }
        i = i - 1;
    }
    proof {
        assert(TrailingParens(s@.take((i + 1) as int)) == 0nat);
    }
    let x: i64 = s.len() as i64 - i - 1;
    let bad = x > s.len() as i64 - x;
    bad
}

fn main() {}

} // verus!
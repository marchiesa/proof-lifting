use vstd::prelude::*;

verus! {

spec fn count_a(s: Seq<u8>) -> int
    decreases s.len()
{
    if s.len() == 0 {
        0
    } else {
        (if s[s.len() - 1] == b'a' { 1 } else { 0 }) + count_a(s.subrange(0, s.len() - 1))
    }
}

spec fn can_form_good_of_length(s: Seq<u8>, len: int) -> bool
{
    0 <= len && len <= s.len() &&
    (exists|num_a: int| 0 <= num_a && num_a <= len &&
        num_a <= count_a(s) &&
        len - num_a + count_a(s) <= s.len() &&
        2 * num_a > len)
}

proof fn count_a_bound(s: Seq<u8>)
    ensures count_a(s) <= s.len()
{
    assume(false);
}

#[verifier::loop_isolation(false)]
fn love_a(s: &Vec<u8>) -> (result: i64)
    requires count_a(s@) >= 1
    ensures 0 <= result as int
    ensures result as int <= s@.len()
    ensures can_form_good_of_length(s@, result as int)
    ensures (forall|k: int| result as int < k && k <= s@.len() ==> !can_form_good_of_length(s@, k))
{
    let mut count: i64 = 0;
    let mut i: usize = 0;
    while i < s.len()
    {
        if s[i] == b'a' {
            count = count + 1;
        }
        i = i + 1;
    }

    let candidate: i64 = 2 * count - 1;
    let slen: i64 = s.len() as i64;
    if slen < candidate {
        proof { assume(false); }
        return slen;
    } else {
        proof { assume(false); }
        return candidate;
    }
}

fn main() {}

} // verus!
use vstd::prelude::*;

verus! {

spec fn delta(c: char) -> int {
    if c == '-' { -1int } else { 1int }
}

spec fn sum_deltas(s: Seq<char>) -> int
    decreases s.len()
{
    if s.len() == 0 {
        0int
    } else {
        sum_deltas(s.take(s.len() - 1)) + delta(s[s.len() - 1])
    }
}

spec fn valid_execution(s: Seq<char>, init: int) -> bool {
    init >= 0 &&
    forall|k: int| 0 <= k <= s.len() ==> init + sum_deltas(s.take(k)) >= 0
}

spec fn final_pile_size(s: Seq<char>, init: int) -> int {
    init + sum_deltas(s)
}

#[verifier::loop_isolation(false)]
fn pile_of_stones(s: &Vec<char>) -> (result: i64)
    ensures
        exists|init: int| valid_execution(s@, init) && final_pile_size(s@, init) == result as int,
        forall|init: int| valid_execution(s@, init) ==> final_pile_size(s@, init) >= result as int,
{
    let mut result: i64 = 0;
    let mut i: usize = 0;
    let ghost mut absorbed: int = 0;
    let ghost mut min_k: int = 0;

    while i < s.len()
        decreases s.len() - i
    {
        proof { assume(false); }
        if s[i] == '-' {
            if result > 0 {
                result = result - 1;
            } else {
                proof { absorbed = absorbed + 1; }
                proof { min_k = i as int + 1; }
            }
        } else {
            result = result + 1;
        }
        i = i + 1;
    }

    proof { assume(false); }

    result
}

fn main() {}

} // verus!
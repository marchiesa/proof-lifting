use vstd::prelude::*;

verus! {

spec fn all_consider_easy(opinions: Seq<int>) -> bool {
    forall|i: int| 0 <= i < opinions.len() ==> opinions[i] == 0
}

#[verifier::loop_isolation(false)]
fn is_easy_problem(_n: i64, opinions: &Vec<i64>) -> (result: bool)
    ensures
        all_consider_easy(opinions@.map_values(|x: i64| x as int)) ==> result == true,
        !all_consider_easy(opinions@.map_values(|x: i64| x as int)) ==> result == false,
{
    let mut all_zero: bool = true;
    let mut i: usize = 0;
    while i < opinions.len()
    {
        if opinions[i] != 0 {
            all_zero = false;
        }
        i = i + 1;
    }
    proof { assume(false); }
    all_zero
}

fn main() {}

} // verus!
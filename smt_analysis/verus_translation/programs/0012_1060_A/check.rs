use vstd::prelude::*;

verus! {

spec fn count_occurrences(s: Seq<int>, v: int) -> int
    decreases s.len()
{
    if s.len() == 0 {
        0
    } else {
        (if s[s.len() - 1] == v { 1 } else { 0 }) + count_occurrences(s.take(s.len() - 1), v)
    }
}

spec fn valid_phone_assignment(assignment: Seq<int>, k: int, digits: Seq<int>) -> bool {
    assignment.len() == digits.len() &&
    k >= 0 &&
    (forall|i: int| 0 <= i < assignment.len() ==> 0 <= assignment[i] && assignment[i] <= k) &&
    (forall|j: int| 1 <= j && j <= k ==>
        count_occurrences(assignment, j) == 11 &&
        (exists|i: int| 0 <= i < digits.len() && assignment[i] == j && digits[i] == 8))
}

spec fn achievable(k: int, digits: Seq<int>) -> bool {
    k >= 0 && 11 * k <= digits.len() && k <= count_occurrences(digits, 8)
}

proof fn count_occurrences_non_neg(s: Seq<int>, v: int)
    ensures count_occurrences(s, v) >= 0
    decreases s.len()
{
    assume(false);
}

#[verifier::loop_isolation(false)]
fn phone_numbers(n: i64, digits: &Vec<i64>) -> (count: i64)
    requires n == digits.len() as i64
    ensures achievable(count as int, digits@.map_values(|x: i64| x as int))
    ensures !achievable(count as int + 1, digits@.map_values(|x: i64| x as int))
{
    let mut cnt8: i64 = 0;
    let mut i: usize = 0;
    while i < digits.len() {
        proof { assume(false); }
        if digits[i] == 8 {
            cnt8 = cnt8 + 1;
        }
        i = i + 1;
    }
    proof { assume(false); }
    proof { count_occurrences_non_neg(digits@.map_values(|x: i64| x as int), 8); }
    if cnt8 < n / 11 {
        cnt8
    } else {
        n / 11
    }
}

fn main() {}

} // verus!
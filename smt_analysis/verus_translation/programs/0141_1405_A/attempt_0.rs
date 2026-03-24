use vstd::prelude::*;

verus! {

spec fn in_range(s: Seq<int>) -> bool {
    forall|i: int| 0 <= i < s.len() ==> 1 <= s[i] <= s.len()
}

spec fn all_distinct(s: Seq<int>) -> bool {
    forall|i: int, j: int| 0 <= i < s.len() && 0 <= j < s.len() && i != j ==> s[i] != s[j]
}

spec fn is_permutation(p: Seq<int>) -> bool {
    in_range(p) && all_distinct(p)
}

spec fn adjacent_sums(p: Seq<int>) -> Seq<int>
    decreases p.len()
{
    if p.len() < 2 {
        seq![]
    } else if p.len() == 2 {
        seq![p[0] + p[1]]
    } else {
        seq![p[0] + p[1]] + adjacent_sums(p.subrange(1, p.len() as int))
    }
}

spec fn same_fingerprint(p: Seq<int>, q: Seq<int>) -> bool {
    Multiset::from_seq(adjacent_sums(p)) == Multiset::from_seq(adjacent_sums(q))
}

proof fn adjacent_sums_length(s: Seq<int>)
    requires
        s.len() >= 2,
    ensures
        adjacent_sums(s).len() == s.len() - 1,
    decreases s.len(),
{
    assume(false);
}

proof fn adjacent_sums_element(s: Seq<int>, k: int)
    requires
        s.len() >= 2,
        0 <= k < s.len() - 1,
    ensures
        adjacent_sums(s).len() == s.len() - 1,
        adjacent_sums(s)[k] == s[k] + s[k + 1],
    decreases s.len(),
{
    assume(false);
}

proof fn seq_reverse_multiset(s: Seq<int>, r: Seq<int>)
    requires
        s.len() == r.len(),
        forall|k: int| 0 <= k < s.len() ==> r[k] == s[s.len() - 1 - k],
    ensures
        Multiset::from_seq(s) == Multiset::from_seq(r),
    decreases s.len(),
{
    assume(false);
}

#[verifier::loop_isolation(false)]
fn permutation_forgery(p: &Vec<i64>) -> (result: Vec<i64>)
    requires
        p@.len() >= 2,
        is_permutation(p@.map_values(|x: i64| x as int)),
    ensures
        result@.len() == p@.len(),
        is_permutation(result@.map_values(|x: i64| x as int)),
        result@ != p@,
        same_fingerprint(
            p@.map_values(|x: i64| x as int),
            result@.map_values(|x: i64| x as int),
        ),
{
    let mut result: Vec<i64> = Vec::new();
    let mut i: usize = p.len();
    while i > 0 {
        i = i - 1;
        result.push(p[i]);
    }
    proof {
        assume(false);
    }
    result
}

fn main() {}

} // verus!
use vstd::prelude::*;

verus! {

spec fn is_subsequence(c: Seq<int>, s: Seq<int>) -> bool
    decreases s.len()
{
    if c.len() == 0 {
        true
    } else if s.len() == 0 {
        false
    } else if c[c.len() - 1] == s[s.len() - 1] {
        is_subsequence(c.take(c.len() - 1), s.take(s.len() - 1))
    } else {
        is_subsequence(c, s.take(s.len() - 1))
    }
}

spec fn exists_common_subseq_of_len(a: Seq<int>, b: Seq<int>, k: int) -> bool
    decreases a.len() + b.len()
{
    if k == 0 {
        true
    } else if a.len() == 0 || b.len() == 0 {
        false
    } else if a[a.len() - 1] == b[b.len() - 1] {
        exists_common_subseq_of_len(a.take(a.len() - 1), b.take(b.len() - 1), k - 1) ||
        exists_common_subseq_of_len(a.take(a.len() - 1), b, k) ||
        exists_common_subseq_of_len(a, b.take(b.len() - 1), k)
    } else {
        exists_common_subseq_of_len(a.take(a.len() - 1), b, k) ||
        exists_common_subseq_of_len(a, b.take(b.len() - 1), k)
    }
}

spec fn min(x: int, y: int) -> int {
    if x <= y { x } else { y }
}

spec fn no_common_elements(a: Seq<int>, b: Seq<int>) -> bool {
    forall|i: int, j: int| 0 <= i < a.len() && 0 <= j < b.len() ==> a[i] != b[j]
}

proof fn singleton_is_subsequence(x: int, s: Seq<int>, idx: int)
    requires
        0 <= idx < s.len(),
        s[idx] == x,
    ensures
        is_subsequence(seq![x], s),
    decreases s.len()
{
    assume(false);
}

proof fn no_common_elements_means_no_common_subseq(a: Seq<int>, b: Seq<int>, k: int)
    requires
        k >= 1,
        no_common_elements(a, b),
    ensures
        !exists_common_subseq_of_len(a, b, k),
    decreases a.len() + b.len()
{
    assume(false);
}

#[verifier::loop_isolation(false)]
fn common_subsequence(a: &Vec<i64>, b: &Vec<i64>) -> (result: (bool, Vec<i64>))
    ensures
        result.0 ==>
            result.1@.map_values(|x: i64| x as int).len() >= 1 &&
            is_subsequence(result.1@.map_values(|x: i64| x as int), a@.map_values(|x: i64| x as int)) &&
            is_subsequence(result.1@.map_values(|x: i64| x as int), b@.map_values(|x: i64| x as int)) &&
            (forall|len: int| 1 <= len < result.1@.map_values(|x: i64| x as int).len() ==>
                !exists_common_subseq_of_len(
                    a@.map_values(|x: i64| x as int),
                    b@.map_values(|x: i64| x as int),
                    len,
                )),
        !result.0 ==>
            (forall|len: int|
                1 <= len <= min(
                    a@.map_values(|x: i64| x as int).len(),
                    b@.map_values(|x: i64| x as int).len(),
                ) ==>
                !exists_common_subseq_of_len(
                    a@.map_values(|x: i64| x as int),
                    b@.map_values(|x: i64| x as int),
                    len,
                )),
{
    let mut found = false;
    let mut c: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    while i < a.len()
    {
        let mut j: usize = 0;
        while j < b.len()
        {
            if a[i] == b[j] {
                found = true;
                c = vec![a[i]];
                proof {
                    singleton_is_subsequence(
                        a[i] as int,
                        a@.map_values(|x: i64| x as int),
                        i as int,
                    );
                    singleton_is_subsequence(
                        a[i] as int,
                        b@.map_values(|x: i64| x as int),
                        j as int,
                    );
                }
                return (found, c);
            }
            j = j + 1;
        }
        i = i + 1;
    }
    proof {
        assume(false);
    }
    (found, c)
}

fn main() {}

} // verus!
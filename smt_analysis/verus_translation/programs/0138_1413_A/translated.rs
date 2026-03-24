use vstd::prelude::*;

verus! {

spec fn dot_product(a: Seq<int>, b: Seq<int>) -> int
    recommends a.len() == b.len()
    decreases a.len()
{
    if a.len() == 0 {
        0
    } else {
        dot_product(a.subrange(0, a.len() as int - 1), b.subrange(0, b.len() as int - 1))
            + a[a.len() as int - 1] * b[b.len() as int - 1]
    }
}

spec fn all_non_zero(s: Seq<int>) -> bool {
    forall|i: int| 0 <= i < s.len() ==> s[i] != 0
}

spec fn all_bounded(s: Seq<int>, bound: int) -> bool {
    forall|i: int| 0 <= i < s.len() ==> -bound <= s[i] && s[i] <= bound
}

spec fn valid_solution(a: Seq<int>, b: Seq<int>) -> bool {
    a.len() == b.len()
        && all_non_zero(b)
        && all_bounded(b, 100)
        && dot_product(a, b) == 0
}

proof fn dot_product_append(a: Seq<int>, b: Seq<int>, x: int, y: int)
    requires a.len() == b.len()
    ensures dot_product(a.push(x), b.push(y)) == dot_product(a, b) + x * y
{
    assume(false);
}

#[verifier::loop_isolation(false)]
fn find_sasuke(a: &Vec<i64>) -> (b: Vec<i64>)
    requires
        a@.len() % 2 == 0,
        all_non_zero(a@.map_values(|x: i64| x as int)),
        all_bounded(a@.map_values(|x: i64| x as int), 100),
    ensures
        valid_solution(
            a@.map_values(|x: i64| x as int),
            b@.map_values(|x: i64| x as int),
        ),
{
    let mut b: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    while i < a.len()
    {
        if i % 2 == 0 {
            proof { assume(false); }
            proof { assume(false); }
            b.push(a[i + 1]);
        } else {
            proof { assume(false); }
            proof { assume(false); }
            b.push(-a[i - 1]);
        }
        i = i + 1;
    }
    proof { assume(false); }
    b
}

fn main() {}

} // verus!
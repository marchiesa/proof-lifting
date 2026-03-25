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
    let a2 = a.push(x);
    let b2 = b.push(y);
    assert(a2.subrange(0, a2.len() as int - 1) =~= a);
    assert(b2.subrange(0, b2.len() as int - 1) =~= b);
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
    let ghost a_spec = a@.map_values(|x: i64| x as int);
    let mut b: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            b@.len() == i as nat,
            a_spec =~= a@.map_values(|x: i64| x as int),
            a@.len() % 2 == 0,
            all_non_zero(a_spec),
            all_bounded(a_spec, 100),
            all_non_zero(b@.map_values(|x: i64| x as int)),
            all_bounded(b@.map_values(|x: i64| x as int), 100),
            (i as int) % 2 == 0 ==> dot_product(a_spec.take(i as int), b@.map_values(|x: i64| x as int)) == 0,
            (i as int) % 2 == 1 ==> dot_product(a_spec.take(i as int), b@.map_values(|x: i64| x as int)) == a_spec[(i as int) - 1] * a_spec[i as int],
        decreases a.len() - i,
    {
        let ghost b_spec = b@.map_values(|x: i64| x as int);
        if i % 2 == 0 {
            proof {
                dot_product_append(a_spec.take(i as int), b_spec, a_spec[i as int], a_spec[(i as int) + 1]);
                assert(a_spec.take(i as int).push(a_spec[i as int]) =~= a_spec.take((i as int) + 1));
            }
            b.push(a[i + 1]);
            proof {
                assert(b@.map_values(|x: i64| x as int) =~= b_spec.push(a_spec[(i as int) + 1]));
            }
        } else {
            proof {
                dot_product_append(a_spec.take(i as int), b_spec, a_spec[i as int], -a_spec[(i as int) - 1]);
                assert(a_spec.take(i as int).push(a_spec[i as int]) =~= a_spec.take((i as int) + 1));
            }
            b.push(-a[i - 1]);
            proof {
                assert(b@.map_values(|x: i64| x as int) =~= b_spec.push(-a_spec[(i as int) - 1]));
            }
        }
        i = i + 1;
    }
    proof {
        assert(a_spec.take(a_spec.len()) =~= a_spec);
    }
    b
}

fn main() {}

} // verus!
use vstd::prelude::*;

verus! {

spec fn FrogPosition(a: int, b: int, k: nat) -> int
    decreases k
{
    if k == 0 {
        0
    } else if (k - 1) % 2 == 0 {
        FrogPosition(a, b, (k - 1) as nat) + a
    } else {
        FrogPosition(a, b, (k - 1) as nat) - b
    }
}

proof fn FrogPositionClosedForm(a: int, b: int, k: nat)
    ensures FrogPosition(a, b, k) ==
        (k / 2) * a - (k / 2) * b + (if k % 2 == 1 { a } else { 0 })
    decreases k
{
    if k == 0 {
    } else if k == 1 {
    } else {
        FrogPositionClosedForm(a, b, (k - 1) as nat);
        if (k - 1) % 2 == 0 {
            assert((k - 1) / 2 == k / 2);
        } else {
            assert((k - 1) / 2 + 1 == k / 2);
        }
    }
}

#[verifier::loop_isolation(false)]
fn FrogJumping(queries: &Vec<(i64, i64, i64)>) -> (results: Vec<i64>)
    requires
        forall|i: int| #![trigger queries@[i]] 0 <= i < queries@.len() ==> queries@[i].2 >= 0,
        forall|i: int| #![trigger queries@[i]] 0 <= i < queries@.len() ==> {
            let a = queries@[i].0 as int;
            let b = queries@[i].1 as int;
            let k = queries@[i].2 as int;
            let half = k / 2;
            i64::MIN <= a * half && a * half <= i64::MAX
            && i64::MIN <= b * half && b * half <= i64::MAX
            && i64::MIN <= a * half - b * half && a * half - b * half <= i64::MAX
            && (k % 2 == 1 ==>
                i64::MIN <= a * half - b * half + a && a * half - b * half + a <= i64::MAX)
        },
    ensures
        results@.len() == queries@.len(),
        forall|i: int| #![trigger results@[i]] 0 <= i < queries@.len() ==>
            results@[i] as int == FrogPosition(
                queries@[i].0 as int,
                queries@[i].1 as int,
                queries@[i].2 as nat,
            ),
{
    let mut results: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    while i < queries.len()
        invariant
            0 <= i <= queries@.len(),
            results@.len() == i as int,
            forall|j: int| #![trigger results@[j]] 0 <= j < i as int ==>
                results@[j] as int == FrogPosition(
                    queries@[j].0 as int,
                    queries@[j].1 as int,
                    queries@[j].2 as nat,
                ),
        decreases queries.len() - i,
    {
        let (a, b, k) = queries[i];
        let half = k / 2;
        let mut ans: i64 = a * half - b * half;
        if k % 2 == 1 {
            ans = ans + a;
        }
        proof {
            FrogPositionClosedForm(a as int, b as int, k as nat);
        }
        results.push(ans);
        i = i + 1;
    }
    results
}

fn main() {}

} // verus!
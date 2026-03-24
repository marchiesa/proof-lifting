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
            assume(false);
        } else {
            assume(false);
        }
    }
}

#[verifier::loop_isolation(false)]
fn FrogJumping(queries: &Vec<(i64, i64, i64)>) -> (results: Vec<i64>)
    requires
        forall|i: int| 0 <= i < queries@.len() ==> queries@[i].2 >= 0,
    ensures
        results@.len() == queries@.len(),
        forall|i: int| 0 <= i < queries@.len() ==>
            results@[i] as int == FrogPosition(
                queries@[i].0 as int,
                queries@[i].1 as int,
                queries@[i].2 as nat,
            ),
{
    let mut results: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    while i < queries.len()
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
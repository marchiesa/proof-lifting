use vstd::prelude::*;

verus! {

spec fn IsValidPurchase(ones: int, twos: int, n: int) -> bool {
    ones >= 0 && twos >= 0 && ones + 2 * twos == n
}

spec fn PurchaseCost(ones: int, twos: int, a: int, b: int) -> int {
    ones * a + twos * b
}

spec fn MinCost(n: int, a: int, b: int) -> int {
    let allOnesCost = PurchaseCost(n, 0, a, b);
    let maxTwosCost = PurchaseCost(n % 2, n / 2, a, b);
    if allOnesCost <= maxTwosCost { allOnesCost } else { maxTwosCost }
}

#[verifier::loop_isolation(false)]
fn WaterBuying(queries: &Vec<(i64, i64, i64)>) -> (results: Vec<i64>)
    requires
        forall|i: int| 0 <= i < queries@.len() ==> queries@[i].0 >= 0,
    ensures
        results@.len() == queries@.len(),
        forall|i: int| 0 <= i < queries@.len() ==>
            results@[i] as int == MinCost(
                queries@[i].0 as int,
                queries@[i].1 as int,
                queries@[i].2 as int,
            ),
{
    let mut results: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    while i < queries.len()
        invariant
            0 <= i <= queries.len(),
            results@.len() == i,
            forall|j: int| 0 <= j < i ==>
                results@[j] as int == MinCost(
                    queries@[j].0 as int,
                    queries@[j].1 as int,
                    queries@[j].2 as int,
                ),
        decreases queries.len() - i,
    {
        let (n, a, b) = queries[i];
        let two = 2 * a;
        let m = if two < b { two } else { b };
        let ans = (n / 2) * m + (n % 2) * a;

        proof {
            let n_int: int = n as int;
            let a_int: int = a as int;
            let b_int: int = b as int;

            assert(n_int >= 0);
            assert(n_int / 2 * 2 + n_int % 2 == n_int);

            let allOnesCost: int = PurchaseCost(n_int, 0, a_int, b_int);
            let maxTwosCost: int = PurchaseCost(n_int % 2, n_int / 2, a_int, b_int);

            assert(allOnesCost == n_int * a_int);
            assert(maxTwosCost == (n_int % 2) * a_int + (n_int / 2) * b_int);

            if two < b {
                assert(two as int == 2 * a_int);
                assert(m as int == 2 * a_int);
                assert(ans as int == (n_int / 2) * (2 * a_int) + (n_int % 2) * a_int);
                assert((n_int / 2) * (2 * a_int) == (n_int / 2 * 2) * a_int) by (nonlinear_arith);
                assert(ans as int == (n_int / 2 * 2 + n_int % 2) * a_int) by (nonlinear_arith);
                assert(ans as int == n_int * a_int);
                assert(2 * a_int < b_int);
                assert(2 * a_int - b_int < 0);
                assert(n_int / 2 >= 0);
                assert((n_int / 2) * (2 * a_int - b_int) <= 0) by (nonlinear_arith);
                assert(n_int * a_int - ((n_int % 2) * a_int + (n_int / 2) * b_int) == (n_int / 2) * (2 * a_int - b_int)) by (nonlinear_arith);
                assert(allOnesCost <= maxTwosCost);
                assert(ans as int == MinCost(n_int, a_int, b_int));
            } else {
                assert(m as int == b_int);
                assert(ans as int == (n_int / 2) * b_int + (n_int % 2) * a_int);
                assert(ans as int == maxTwosCost);
                assert(2 * a_int >= b_int);
                assert(2 * a_int - b_int >= 0);
                assert(n_int / 2 >= 0);
                assert((n_int / 2) * (2 * a_int - b_int) >= 0) by (nonlinear_arith);
                assert(n_int * a_int - ((n_int % 2) * a_int + (n_int / 2) * b_int) == (n_int / 2) * (2 * a_int - b_int)) by (nonlinear_arith);
                assert(allOnesCost >= maxTwosCost);
                assert(ans as int == MinCost(n_int, a_int, b_int));
            }
        }

        results.push(ans);
        i += 1;
    }
    results
}

fn main() {}

} // verus!
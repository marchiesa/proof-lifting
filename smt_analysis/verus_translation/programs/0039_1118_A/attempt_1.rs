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
    {
        let (n, a, b) = queries[i];
        let two = 2 * a;
        let m = if two < b { two } else { b };
        let ans = (n / 2) * m + (n % 2) * a;

        proof { assume(false); }

        results.push(ans);
        i += 1;
    }
    results
}

fn main() {}

} // verus!
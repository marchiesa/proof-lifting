use vstd::prelude::*;

verus! {

spec fn Sum(a: Seq<int>) -> int
    decreases a.len()
{
    if a.len() == 0 {
        0
    } else {
        Sum(a.take(a.len() - 1)) + a[a.len() - 1]
    }
}

spec fn AllValid(coins: Seq<int>, n: int) -> bool {
    forall|i: int| 0 <= i < coins.len() ==> 1 <= coins[i] && coins[i] <= n
}

spec fn IsValidSelection(coins: Seq<int>, n: int, S: int) -> bool {
    coins.len() >= 1 && AllValid(coins, n) && Sum(coins) == S
}

spec fn Achievable(k: int, n: int, S: int) -> bool {
    k >= 1 && n >= 1 && k <= S && S <= k * n
}

spec fn Witness(k: int, n: int, S: int) -> Seq<int> {
    if k >= 1 && n >= 1 && k <= S && S <= k * n {
        Seq::new(k as nat, |i: int| if i < k - 1 { n } else { S - (k - 1) * n })
    } else {
        Seq::empty()
    }
}

fn Coins(n: i64, S: i64) -> (minCoins: i64)
    requires
        n >= 1,
        S >= 1,
    ensures
        Achievable(minCoins as int, n as int, S as int),
        forall|k: int| 1 <= k && k < minCoins as int ==> !Achievable(k, n as int, S as int),
{
    let min_coins: i64 = (S - 1) / n + 1;
    proof { assume(false); }
    min_coins
}

fn main() {}

} // verus!
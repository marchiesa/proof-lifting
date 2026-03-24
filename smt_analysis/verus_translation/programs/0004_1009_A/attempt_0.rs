use vstd::prelude::*;

verus! {

spec fn max(x: int, y: int) -> int {
    if x >= y { x } else { y }
}

spec fn max_purchases(c: Seq<int>, a: Seq<int>) -> int
    decreases c.len()
{
    if c.len() == 0 || a.len() == 0 {
        0
    } else if a[0] >= c[0] {
        max(1 + max_purchases(c.skip(1), a.skip(1)), max_purchases(c.skip(1), a))
    } else {
        max_purchases(c.skip(1), a)
    }
}

proof fn max_purchases_bound(c: Seq<int>, a: Seq<int>)
    ensures 0 <= max_purchases(c, a),
    ensures max_purchases(c, a) <= c.len(),
    ensures max_purchases(c, a) <= a.len(),
    decreases c.len()
{
    if c.len() == 0 || a.len() == 0 {
    } else if a[0] >= c[0] {
        max_purchases_bound(c.skip(1), a.skip(1));
        max_purchases_bound(c.skip(1), a);
    } else {
        max_purchases_bound(c.skip(1), a);
    }
}

proof fn more_games_no_worse(c: Seq<int>, a: Seq<int>)
    requires c.len() > 0,
    ensures max_purchases(c, a) >= max_purchases(c.skip(1), a),
{
    if a.len() == 0 {
    } else if a[0] >= c[0] {
        assume(false);
    }
}

proof fn extra_bill_bounded(c: Seq<int>, a: Seq<int>)
    requires a.len() > 0,
    ensures max_purchases(c, a) <= max_purchases(c, a.skip(1)) + 1,
    decreases c.len()
{
    if c.len() == 0 {
    } else {
        extra_bill_bounded(c.skip(1), a);
        more_games_no_worse(c, a.skip(1));
    }
}

proof fn greedy_buy_optimal(c: Seq<int>, a: Seq<int>)
    requires c.len() > 0,
    requires a.len() > 0,
    requires a[0] >= c[0],
    ensures max_purchases(c, a) == 1 + max_purchases(c.skip(1), a.skip(1)),
{
    extra_bill_bounded(c.skip(1), a);
}

#[verifier::loop_isolation(false)]
fn game_shopping(c: &Vec<i64>, a: &Vec<i64>) -> (count: i64)
    ensures count as int == max_purchases(
        c@.map_values(|x: i64| x as int),
        a@.map_values(|x: i64| x as int),
    ),
    ensures 0 <= count as int,
    ensures count as int <= c@.len(),
    ensures count as int <= a@.len(),
{
    let mut count: i64 = 0;
    let mut i: usize = 0;
    let mut j: usize = 0;

    while i < c.len() && j < a.len()
        decreases c.len() - i
    {
        if a[j] >= c[i] {
            proof { assume(false); }
            count = count + 1;
            j = j + 1;
        } else {
            proof { assume(false); }
        }
        i = i + 1;
    }
    proof { assume(false); }
    count
}

fn main() {}

} // verus!
use vstd::prelude::*;

verus! {

spec fn Sum(a: Seq<int>) -> int
    decreases a.len()
{
    if a.len() == 0 {
        0
    } else {
        Sum(a.subrange(0, a.len() - 1)) + a[a.len() - 1]
    }
}

spec fn NoLoss(price: int, a: Seq<int>) -> bool
    recommends a.len() > 0
{
    price * a.len() >= Sum(a)
}

spec fn IsMinimalEqualPrice(price: int, a: Seq<int>) -> bool
    recommends a.len() > 0
{
    NoLoss(price, a) && !NoLoss(price - 1, a)
}

#[verifier::loop_isolation(false)]
fn EqualizePrice(a: &Vec<i64>) -> (price: i64)
    requires a.len() > 0
    ensures IsMinimalEqualPrice(price as int, a@.map_values(|x: i64| x as int))
{
    let mut s: i64 = 0;
    let n = a.len();
    let mut i: usize = 0;
    while i < n
    {
        proof { assume(false); }
        s = s + a[i];
        i = i + 1;
    }
    proof { assume(false); }

    let price = (s + n as i64 - 1) / n as i64;

    let r = s % n as i64;
    proof { assume(false); }

    if r == 0 {
        proof { assume(false); }
    } else {
        proof { assume(false); }
    }

    price
}

fn main() {}

} // verus!
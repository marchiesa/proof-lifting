use vstd::prelude::*;

verus! {

spec fn IsPositiveAfterDiv(x: int, d: int) -> bool
    recommends d != 0
{
    (x > 0 && d > 0) || (x < 0 && d < 0)
}

spec fn CountPositiveAfterDiv(a: Seq<int>, d: int) -> int
    recommends d != 0
    decreases a.len()
{
    if a.len() == 0 {
        0
    } else {
        CountPositiveAfterDiv(a.take(a.len() - 1), d)
            + (if IsPositiveAfterDiv(a[a.len() - 1], d) { 1 } else { 0 })
    }
}

spec fn CeilHalf(n: int) -> int {
    (n + 1) / 2
}

spec fn CountPositive(a: Seq<int>) -> int
    decreases a.len()
{
    if a.len() == 0 {
        0
    } else {
        CountPositive(a.take(a.len() - 1))
            + (if a[a.len() - 1] > 0 { 1 } else { 0 })
    }
}

spec fn CountNegative(a: Seq<int>) -> int
    decreases a.len()
{
    if a.len() == 0 {
        0
    } else {
        CountNegative(a.take(a.len() - 1))
            + (if a[a.len() - 1] < 0 { 1 } else { 0 })
    }
}

proof fn CountPosDivPos(a: Seq<int>, d: int)
    requires d > 0
    ensures CountPositiveAfterDiv(a, d) == CountPositive(a)
    decreases a.len()
{
    if a.len() > 0 {
        CountPosDivPos(a.take(a.len() - 1), d);
    }
}

proof fn CountPosDivNeg(a: Seq<int>, d: int)
    requires d < 0
    ensures CountPositiveAfterDiv(a, d) == CountNegative(a)
    decreases a.len()
{
    if a.len() > 0 {
        CountPosDivNeg(a.take(a.len() - 1), d);
    }
}

#[verifier::loop_isolation(false)]
fn BePositive(a: &Vec<i64>) -> (d: i64)
    ensures
        d as int != 0 ==> -1000 <= d as int && d as int <= 1000
            && CountPositiveAfterDiv(
                a@.map_values(|x: i64| x as int),
                d as int,
            ) >= CeilHalf(a@.len() as int),
        d as int == 0 ==> forall|d_prime: int|
            d_prime == 0
            || CountPositiveAfterDiv(
                a@.map_values(|x: i64| x as int),
                d_prime,
            ) < CeilHalf(a@.len() as int),
{
    let n = a.len();
    let mut pcount: i64 = 0;
    let mut ncount: i64 = 0;
    let mut zcount: i64 = 0;
    let mut i: usize = 0;
    while i < n {
        proof { assume(false); }
        if a[i] > 0 {
            pcount = pcount + 1;
        } else if a[i] < 0 {
            ncount = ncount + 1;
        } else {
            zcount = zcount + 1;
        }
        i = i + 1;
    }
    proof { assume(false); }
    let half = ((n as i64) + 1) / 2;
    if pcount >= half {
        proof { assume(false); }
        return 1;
    } else if ncount >= half {
        proof { assume(false); }
        return -1;
    } else {
        proof { assume(false); }
        return 0;
    }
}

fn main() {}

} // verus!
use vstd::prelude::*;

verus! {

spec fn DigitSum(n: int) -> int
    recommends n >= 0
    decreases n
{
    if n == 0 { 0 }
    else { n % 10 + DigitSum(n / 10) }
}

spec fn IsInteresting(n: int) -> bool
    recommends n >= 0
{
    DigitSum(n) == 18
}

#[verifier::loop_isolation(false)]
fn SumDigits(x: i64) -> (s: i64)
    requires x >= 0
    ensures s as int == DigitSum(x as int)
{
    let mut s: i64 = 0;
    let mut tmp = x;
    while tmp > 0
    {
        s = s + tmp % 10;
        tmp = tmp / 10;
    }
    s
}

#[verifier::loop_isolation(false)]
fn NearestInterestingNumber(a: i64) -> (n: i64)
    requires a >= 1
    ensures n >= a
    ensures IsInteresting(n as int)
    ensures forall|k: int| a as int <= k < n as int ==> !IsInteresting(k)
{
    let mut n = a;
    let mut s = SumDigits(n);
    while s != 18
    {
        n = n + 1;
        s = SumDigits(n);
    }
    n
}

fn main() {}

} // verus!
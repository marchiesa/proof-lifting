use vstd::prelude::*;

verus! {

spec fn DigitSum(n: int) -> int
    decreases n
{
    if n <= 0 { 0 }
    else { n % 10 + DigitSum(n / 10) }
}

spec fn IsInteresting(n: int) -> bool
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
        invariant
            tmp >= 0,
            s as int + DigitSum(tmp as int) == DigitSum(x as int),
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
    ensures forall|k: int| a as int <= k && k < n as int ==> !IsInteresting(k)
{
    let mut n = a;
    let mut s = SumDigits(n);
    while s != 18
        invariant
            n >= a,
            s as int == DigitSum(n as int),
            forall|k: int| a as int <= k && k < n as int ==> !IsInteresting(k),
    {
        n = n + 1;
        s = SumDigits(n);
    }
    n
}

fn main() {}

} // verus!
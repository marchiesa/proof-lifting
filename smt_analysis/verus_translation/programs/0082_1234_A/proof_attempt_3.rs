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
    let ghost seq = a@.map_values(|x: i64| x as int);
    let mut s: i64 = 0;
    let n = a.len();
    let mut i: usize = 0;
    while i < n
        invariant
            0 <= i <= n,
            s as int == Sum(seq.take(i as int)),
        decreases n - i
    {
        proof {
            let t = seq.take(i as int + 1);
            assert(t.subrange(0, i as int) =~= seq.take(i as int));
            assert(t[i as int] == seq[i as int]);
            assert(t.subrange(0, t.len() as int - 1) =~= seq.take(i as int));
            assert(Sum(t) == Sum(seq.take(i as int)) + seq[i as int]);
        }
        s = s + a[i];
        i = i + 1;
    }
    proof {
        assert(seq.take(n as int) =~= seq);
    }

    let price = (s + n as i64 - 1) / n as i64;
    let r = s % n as i64;

    proof {
        let p = price as int;
        let sv = s as int;
        let nv = n as int;
        let rv = r as int;

        assert(sv == Sum(seq));
        assert(nv > 0);
        assert(sv == (sv / nv) * nv + rv) by (nonlinear_arith);
        assert(0 <= rv < nv) by (nonlinear_arith);

        if r == 0 {
            assert(rv == 0);
            assert(sv + nv - 1 == (sv / nv) * nv + (nv - 1)) by (nonlinear_arith);
            assert(0 <= nv - 1 < nv);
            assert((sv + nv - 1) / nv == sv / nv) by (nonlinear_arith);
            assert(p == sv / nv) by (nonlinear_arith);
            assert(p * nv == sv) by (nonlinear_arith);
            assert(p * nv >= Sum(seq));
            assert((p - 1) * nv == sv - nv) by (nonlinear_arith);
            assert((p - 1) * nv < Sum(seq));
        } else {
            assert(rv != 0);
            assert(rv > 0) by (nonlinear_arith);
            assert(sv + nv - 1 == (sv / nv + 1) * nv + (rv - 1)) by (nonlinear_arith);
            assert(0 <= rv - 1 < nv) by (nonlinear_arith);
            assert((sv + nv - 1) / nv == sv / nv + 1) by (nonlinear_arith);
            assert(p == sv / nv + 1) by (nonlinear_arith);
            assert(p * nv == sv - rv + nv) by (nonlinear_arith);
            assert(p * nv >= sv) by (nonlinear_arith);
            assert(p * nv >= Sum(seq));
            assert((p - 1) * nv == sv - rv) by (nonlinear_arith);
            assert((p - 1) * nv < sv) by (nonlinear_arith);
            assert((p - 1) * nv < Sum(seq));
        }
    }

    price
}

fn main() {}

} // verus!
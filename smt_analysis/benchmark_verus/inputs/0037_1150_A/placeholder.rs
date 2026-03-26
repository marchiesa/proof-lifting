use vstd::prelude::*;

verus! {

pub open spec fn outcome(r: int, buy_price: int, sell_price: int, shares: int) -> int {
    r - shares * buy_price + shares * sell_price
}

pub open spec fn valid_trade(r: int, buy_price: int, shares: int) -> bool {
    buy_price > 0 && shares >= 0 && shares * buy_price <= r
}

pub open spec fn is_achievable(result: int, r: int, s: Seq<int>, b: Seq<int>) -> bool {
    result == r
    ||
    exists|i: int, j: int, k: nat|
        #![trigger outcome(r, s[i], b[j], k as int)]
        0 <= i < s.len() && 0 <= j < b.len()
        && valid_trade(r, s[i], k as int) && result == outcome(r, s[i], b[j], k as int)
}

pub open spec fn is_optimal(result: int, r: int, s: Seq<int>, b: Seq<int>) -> bool {
    result >= r
    &&
    forall|i: int, j: int, k: nat|
        #![trigger outcome(r, s[i], b[j], k as int)]
        0 <= i < s.len() && 0 <= j < b.len() && valid_trade(r, s[i], k as int)
        ==> outcome(r, s[i], b[j], k as int) <= result
}

proof fn div_bound(k: nat, a: int, r: int)
    requires
        a > 0,
        k as int * a <= r,
    ensures
        k <= r / a,
{
    if k > r / a {
        let kk = k as int;
        assert(kk >= r / a + 1);
        assert((r / a + 1) * a == (r / a) * a + a) by(nonlinear_arith)
            requires a > 0;
        assert(r == (r / a) * a + r % a) by(nonlinear_arith)
            requires a > 0;
        assert(0 <= r % a < a) by(nonlinear_arith)
            requires a > 0;
        assert(kk * a >= (r / a + 1) * a) by(nonlinear_arith)
            requires kk >= r / a + 1, a > 0;
        assert((r / a + 1) * a > r) by(nonlinear_arith)
            requires
                r == (r / a) * a + r % a,
                0 <= r % a < a,
                (r / a + 1) * a == (r / a) * a + a;
    }
}

proof fn mul_mono_left(c: int, a: int, b: int)
    requires
        c >= 0,
        a <= b,
    ensures
        c * a <= c * b,
{
    assert(c * a <= c * b) by(nonlinear_arith)
        requires c >= 0, a <= b;
}

proof fn mul_mono_right(a: int, b: int, c: int)
    requires
        a <= b,
        c >= 0,
    ensures
        a * c <= b * c,
{
    assert(a * c <= b * c) by(nonlinear_arith)
        requires a <= b, c >= 0;
}

fn stock_arbitraging(n: i64, m: i64, r: i64, s: &Vec<i64>, b: &Vec<i64>) -> (max_bourles: i64)
    requires
        s@.len() == n as int,
        n >= 1,
        b@.len() == m as int,
        m >= 1,
        r >= 1,
        forall|i: int| 0 <= i < n as int ==> s@[i] >= 1,
        forall|j: int| 0 <= j < m as int ==> b@[j] >= 1,
        // Overflow bounds
        n <= 100_000,
        m <= 100_000,
        r <= 1_000_000_000,
        forall|i: int| 0 <= i < n as int ==> s@[i] <= 1_000_000_000,
        forall|j: int| 0 <= j < m as int ==> b@[j] <= 1_000_000_000,
    ensures
        is_achievable(max_bourles as int, r as int, s@.map_values(|v: i64| v as int), b@.map_values(|v: i64| v as int)),
        is_optimal(max_bourles as int, r as int, s@.map_values(|v: i64| v as int), b@.map_values(|v: i64| v as int)),
{
    let ghost s_spec: Seq<int> = s@.map_values(|v: i64| v as int);
    let ghost b_spec: Seq<int> = b@.map_values(|v: i64| v as int);
    let ghost r_int: int = r as int;

    let mut min_s: i64 = s[0];
    let ghost mut min_idx: int = 0;
    let mut i: usize = 1;

    while i < s.len()
        invariant
            1 <= i <= s.len(),
            0 <= min_idx < i as int,
            min_s as int == s_spec[min_idx],
            forall|k: int| 0 <= k < i as int ==> min_s as int <= s_spec[k],
            s_spec == s@.map_values(|v: i64| v as int),
            s@.len() == n as int,
            n >= 1,
            min_s >= 1,
            min_s <= 1_000_000_000,
            forall|ii: int| 0 <= ii < n as int ==> s@[ii] >= 1,
            forall|ii: int| 0 <= ii < n as int ==> s@[ii] <= 1_000_000_000,
        decreases s.len() - i,
    {
        if s[i] < min_s {
            min_s = s[i];
            proof { min_idx = i as int; }
        }
        i = i + 1;
    }

    let mut max_b: i64 = b[0];
    let ghost mut max_idx: int = 0;
    i = 1;

    while i < b.len()
        invariant
            1 <= i <= b.len(),
            0 <= max_idx < i as int,
            max_b as int == b_spec[max_idx],
            forall|k: int| 0 <= k < i as int ==> max_b as int >= b_spec[k],
            b_spec == b@.map_values(|v: i64| v as int),
            b@.len() == m as int,
            m >= 1,
            max_b >= 1,
            max_b <= 1_000_000_000,
            forall|jj: int| 0 <= jj < m as int ==> b@[jj] >= 1,
            forall|jj: int| 0 <= jj < m as int ==> b@[jj] <= 1_000_000_000,
        decreases b.len() - i,
    {
        if b[i] > max_b {
            max_b = b[i];
            proof { max_idx = i as int; }
        }
        i = i + 1;
    }

    let ghost min_s_int: int = min_s as int;
    let ghost max_b_int: int = max_b as int;
    let ghost shares: nat = (r_int / min_s_int) as nat;
    let ghost shares_int: int = shares as int;

    // r % min_s + (r / min_s) * max_b
    // Overflow proof: r/min_s <= r <= 10^9, max_b <= 10^9
    proof {
        let ri = r_int;
        let ms = min_s_int;
        let mb = max_b_int;
        assert(ri / ms <= ri) by(nonlinear_arith)
            requires ri >= 1, ms >= 1;
        // PLACEHOLDER_0: insert assertion here

        assert(1_000_000_000 * 1_000_000_000 < 0x7FFF_FFFF_FFFF_FFFFi64 as int);
        assert(ri % ms < ms) by(nonlinear_arith)
            requires ms >= 1;
        assert(ri % ms >= 0) by(nonlinear_arith)
            requires ms >= 1;
        assert(ri % ms + (ri / ms) * mb < 0x7FFF_FFFF_FFFF_FFFFi64 as int) by(nonlinear_arith)
            requires
                ri % ms < ms,
                ms <= 1_000_000_000,
                (ri / ms) * mb <= 1_000_000_000 * 1_000_000_000,
                1_000_000_000 * 1_000_000_000 < 0x7FFF_FFFF_FFFF_FFFFi64 as int;
    }
    let profit: i64 = (r % min_s) + (r / min_s) * max_b;

    if profit > r {
        let max_bourles: i64 = profit;
        let ghost mb_int: int = max_bourles as int;

        proof {
            // Prove IsAchievable
            assert(shares_int == r_int / min_s_int);
            // PLACEHOLDER_1: insert assertion here

            assert(shares_int * min_s_int <= r_int) by(nonlinear_arith)
                requires
                    r_int == shares_int * min_s_int + r_int % min_s_int,
                    r_int % min_s_int >= 0,
                    min_s_int > 0;

            assert(s_spec[min_idx] == min_s_int);
            assert(b_spec[max_idx] == max_b_int);
            assert(0 <= min_idx < s_spec.len());
            assert(0 <= max_idx < b_spec.len());

            assert(valid_trade(r_int, s_spec[min_idx], shares_int));

            assert(r_int - shares_int * min_s_int == r_int % min_s_int) by(nonlinear_arith)
                requires
                    min_s_int > 0,
                    r_int == shares_int * min_s_int + r_int % min_s_int;

            assert(outcome(r_int, s_spec[min_idx], b_spec[max_idx], shares_int) == mb_int) by(nonlinear_arith)
                requires
                    s_spec[min_idx] == min_s_int,
                    b_spec[max_idx] == max_b_int,
                    mb_int == r_int % min_s_int + (r_int / min_s_int) * max_b_int,
                    shares_int == r_int / min_s_int,
                    r_int - shares_int * min_s_int == r_int % min_s_int;

            // Trigger the existential for is_achievable
            let witness_i = min_idx;
            let witness_j = max_idx;
            let witness_k = shares;
            assert(0 <= witness_i < s_spec.len());
            assert(0 <= witness_j < b_spec.len());
            assert(valid_trade(r_int, s_spec[witness_i], witness_k as int));
            assert(mb_int == outcome(r_int, s_spec[witness_i], b_spec[witness_j], witness_k as int));

            // Prove IsOptimal
            // PLACEHOLDER_2: insert assertion here





















































        max_bourles
    } else {
        let max_bourles: i64 = r;
        let ghost profit_int: int = profit as int;

        proof {
            // Establish division identity
            // PLACEHOLDER_3: insert assertion here

            let r_div_eq: bool = (r_int == shares_int * min_s_int + r_int % min_s_int);
            assert(r_div_eq);

            // Prove IsOptimal
            // PLACEHOLDER_4: insert assertion here





































































        max_bourles
    }
}

fn main() {}

} // verus!

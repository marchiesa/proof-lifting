use vstd::prelude::*;

verus! {

spec fn CountingSeq(n: int) -> Seq<int>
    decreases n
{
    if n <= 0 { Seq::empty() } else { CountingSeq(n - 1).push(n) }
}

spec fn AllPositive(s: Seq<int>) -> bool {
    forall|i: int| 0 <= i < s.len() ==> (#[trigger] s[i]) >= 1
}

spec fn ConcatStairways(stairs: Seq<int>) -> Seq<int>
    decreases stairs.len()
{
    if stairs.len() == 0 {
        Seq::empty()
    } else {
        ConcatStairways(stairs.take(stairs.len() - 1)).add(
            CountingSeq(stairs[stairs.len() - 1])
        )
    }
}

spec fn IsValidInput(a: Seq<int>) -> bool {
    a.len() >= 1 &&
    a[0] == 1 &&
    forall|i: int| 1 <= i < a.len() ==> ((#[trigger] a[i]) == 1 || a[i] == a[i - 1] + 1)
}

#[verifier::loop_isolation(false)]
fn TanyaAndStairways(a: &Vec<i64>) -> (result: (i64, Vec<i64>))
    requires
        IsValidInput(a@.map_values(|x: i64| x as int)),
    ensures
        result.0 == result.1.len() as i64,
        result.0 >= 1,
        AllPositive(result.1@.map_values(|x: i64| x as int)),
        ConcatStairways(result.1@.map_values(|x: i64| x as int)) == a@.map_values(|x: i64| x as int),
{
    let mut stairs: Vec<i64> = Vec::new();
    let mut cnt: i64 = 0;
    for i in 0..a.len()
        invariant
            a.len() >= 1,
            IsValidInput(a@.map_values(|x: i64| x as int)),
            i == 0usize ==> cnt == 0i64 && stairs@ == Seq::<i64>::empty(),
            i > 0usize ==> cnt as int == (a@.map_values(|x: i64| x as int))[i as int - 1] && cnt >= 1i64,
            AllPositive(stairs@.map_values(|x: i64| x as int)),
            ConcatStairways(stairs@.map_values(|x: i64| x as int)).add(CountingSeq(cnt as int)) == (a@.map_values(|x: i64| x as int)).take(i as int),
    {
        if i == 0 {
            cnt = 1;
        } else if a[i] == 1 {
            proof {
                let stairs_spec = stairs@.map_values(|x: i64| x as int);
                let cnt_int = cnt as int;
                assert(stairs_spec.push(cnt_int).take(stairs_spec.len() as int) =~= stairs_spec);
                assert(ConcatStairways(stairs_spec.push(cnt_int)) == ConcatStairways(stairs_spec).add(CountingSeq(cnt_int)));
                assert forall|j: int| 0 <= j < stairs_spec.push(cnt_int).len() implies (#[trigger] stairs_spec.push(cnt_int)[j]) >= 1 by {
                    if j < stairs_spec.len() {
                        assert(stairs_spec.push(cnt_int)[j] == stairs_spec[j]);
                    } else {
                        assert(stairs_spec.push(cnt_int)[j] == cnt_int);
                    }
                };
                assert(AllPositive(stairs_spec.push(cnt_int)));
            }
            stairs.push(cnt);
            cnt = 1;
        } else {
            proof {
                let cnt_int = cnt as int;
                assert(CountingSeq(cnt_int + 1) == CountingSeq(cnt_int).push(cnt_int + 1));
            }
            cnt = cnt + 1;
        }
    }
    proof {
        let stairs_spec = stairs@.map_values(|x: i64| x as int);
        let a_spec = a@.map_values(|x: i64| x as int);
        assert(a_spec.take(a_spec.len() as int) =~= a_spec);
        assert(stairs_spec.push(cnt as int).take(stairs_spec.len() as int) =~= stairs_spec);
        assert(ConcatStairways(stairs_spec.push(cnt as int)) == ConcatStairways(stairs_spec).add(CountingSeq(cnt as int)));
    }
    stairs.push(cnt);
    let t = stairs.len() as i64;
    (t, stairs)
}

fn main() {}

} // verus!
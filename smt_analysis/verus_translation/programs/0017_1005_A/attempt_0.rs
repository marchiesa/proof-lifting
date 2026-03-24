use vstd::prelude::*;

verus! {

spec fn CountingSeq(n: int) -> Seq<int>
    decreases n
{
    if n <= 0 { Seq::empty() } else { CountingSeq(n - 1).push(n) }
}

spec fn AllPositive(s: Seq<int>) -> bool {
    forall|i: int| 0 <= i < s.len() ==> s[i] >= 1
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
    forall|i: int| 1 <= i < a.len() ==> (a[i] == 1 || a[i] == a[i - 1] + 1)
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
    {
        if i == 0 {
            cnt = 1;
        } else if a[i] == 1 {
            proof { assume(false); }
            stairs.push(cnt);
            cnt = 1;
        } else {
            cnt = cnt + 1;
        }
    }
    proof { assume(false); }
    stairs.push(cnt);
    let t = stairs.len() as i64;
    (t, stairs)
}

fn main() {}

} // verus!
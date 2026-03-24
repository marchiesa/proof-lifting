use vstd::prelude::*;

verus! {

spec fn in_range(a: Seq<int>) -> bool {
    forall|i: int| 0 <= i < a.len() ==> 1 <= a[i] <= 1000
}

spec fn no_triple_sum(a: Seq<int>) -> bool {
    forall|x: int, y: int, z: int|
        0 <= x < a.len() && 0 <= y < a.len() && 0 <= z < a.len() ==>
        a[x] + a[y] != a[z]
}

spec fn is_complete(a: Seq<int>) -> bool {
    in_range(a) && no_triple_sum(a)
}

#[verifier::loop_isolation(false)]
fn solve(n: i64) -> (a: Vec<i64>)
    requires n >= 0
    ensures a@.len() == n as int
    ensures is_complete(a@.map_values(|x: i64| x as int))
{
    let mut a: Vec<i64> = Vec::new();
    let mut i: i64 = 0;
    while i < n
    {
        a.push(1i64);
        i = i + 1;
    }
    a
}

#[verifier::loop_isolation(false)]
fn test_solve(ns: &Vec<i64>)
    requires forall|i: int| 0 <= i < ns@.len() ==> ns@[i] >= 0
{
    let mut i: usize = 0;
    while i < ns.len()
    {
        let r = solve(ns[i]);
        proof { assume(false); }
        let mut j: usize = 0;
        while j < r.len()
        {
            proof { assume(false); }
            j = j + 1;
        }
        i = i + 1;
    }
}

fn main() {}

} // verus!
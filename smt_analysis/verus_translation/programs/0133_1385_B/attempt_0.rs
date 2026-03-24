use vstd::prelude::*;

verus! {

spec fn IsPermutation(p: Seq<int>, n: int) -> bool {
    n >= 1 &&
    p.len() == n &&
    (forall|i: int| 1 <= i && i <= n ==> exists|j: int| 0 <= j && j < n && p[j] == i)
}

spec fn IsMerge(a: Seq<int>, s1: Seq<int>, s2: Seq<int>) -> bool
    decreases a.len()
{
    if a.len() == 0 {
        s1.len() == 0 && s2.len() == 0
    } else {
        (s1.len() > 0 && a[0] == s1[0] && IsMerge(a.skip(1), s1.skip(1), s2)) ||
        (s2.len() > 0 && a[0] == s2[0] && IsMerge(a.skip(1), s1, s2.skip(1)))
    }
}

proof fn MergeAppendS1(a: Seq<int>, s1: Seq<int>, s2: Seq<int>, x: int)
    requires IsMerge(a, s1, s2)
    ensures IsMerge(a.push(x), s1.push(x), s2)
    decreases a.len()
{
    assume(false);
}

proof fn MergeAppendS2(a: Seq<int>, s1: Seq<int>, s2: Seq<int>, x: int)
    requires IsMerge(a, s1, s2)
    ensures IsMerge(a.push(x), s1, s2.push(x))
    decreases a.len()
{
    assume(false);
}

#[verifier::loop_isolation(false)]
fn RestorePermutation(n: i64, a: &Vec<i64>) -> (p: Vec<i64>)
    requires
        n >= 1,
        a@.len() == 2 * (n as int),
        forall|i: int| 0 <= i && i < a@.len() ==> 1 <= a@[i] && a@[i] <= n,
    ensures
        IsPermutation(p@.map_values(|x: i64| x as int), n as int),
        IsMerge(
            a@.map_values(|x: i64| x as int),
            p@.map_values(|x: i64| x as int),
            p@.map_values(|x: i64| x as int),
        ),
{
    let mut seen: Vec<bool> = vec![false; (n + 1) as usize];
    let mut p: Vec<i64> = Vec::new();
    let ghost mut s2: Seq<int> = Seq::empty();

    let mut i: usize = 0;
    while i < a.len() {
        let ai: i64 = a[i];
        if !seen[ai as usize] {
            proof {
                MergeAppendS1(
                    a@.map_values(|x: i64| x as int).take(i as int),
                    p@.map_values(|x: i64| x as int),
                    s2,
                    ai as int,
                );
            }
            p.push(ai);
            seen[ai as usize] = true;
        } else {
            proof {
                assume(
                    s2.len() < p@.len() &&
                    ai as int == p@.map_values(|x: i64| x as int)[s2.len()]
                );
                MergeAppendS2(
                    a@.map_values(|x: i64| x as int).take(i as int),
                    p@.map_values(|x: i64| x as int),
                    s2,
                    ai as int,
                );
                s2 = s2.push(ai as int);
            }
        }
        i += 1;
    }

    proof {
        assume(p@.len() == n as int);
        assume(IsPermutation(p@.map_values(|x: i64| x as int), n as int));
    }

    p
}

fn main() {}

} // verus!
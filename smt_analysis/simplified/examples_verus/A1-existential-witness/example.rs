use vstd::prelude::*;

verus! {

spec fn has_pair(a: Seq<int>, b: Seq<int>) -> bool {
    exists|i: int| 0 <= i < a.len() && 0 <= i < b.len()
        && #[trigger] (a[i] + b[i]) == 0
}

fn find_cancelling(a: &Vec<i64>, b: &Vec<i64>) -> (found: bool)
    requires
        a@.len() == b@.len(),
        a@.len() > 0,
        forall|i: int| 0 <= i < a@.len() ==> -1000 <= #[trigger] a@[i] <= 1000,
        forall|i: int| 0 <= i < b@.len() ==> -1000 <= #[trigger] b@[i] <= 1000,
    ensures
        found ==> has_pair(
            a@.map_values(|x: i64| x as int),
            b@.map_values(|x: i64| x as int),
        ),
{
    let mut found: bool = false;
    let mut j: usize = 0;
    let ghost a_spec = a@.map_values(|x: i64| x as int);
    let ghost b_spec = b@.map_values(|x: i64| x as int);
    while j < a.len()
        invariant
            0 <= j <= a@.len(),
            a@.len() == b@.len(),
            a_spec =~= a@.map_values(|x: i64| x as int),
            b_spec =~= b@.map_values(|x: i64| x as int),
            found ==> has_pair(a_spec, b_spec),
            forall|i: int| 0 <= i < a@.len() ==> -1000 <= #[trigger] a@[i] <= 1000,
            forall|i: int| 0 <= i < b@.len() ==> -1000 <= #[trigger] b@[i] <= 1000,
        decreases a@.len() - j,
    {
        if a[j] + b[j] == 0 {
            proof {
                assert(a_spec[j as int] + b_spec[j as int] == 0);  // QUIRK: existential witness
            }
            found = true;
        }
        j = j + 1;
    }
    found
}

} // verus!

fn main() {}

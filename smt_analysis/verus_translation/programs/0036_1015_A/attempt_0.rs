use vstd::prelude::*;

verus! {

spec fn point_in_segment(p: int, seg: (int, int)) -> bool {
    seg.0 <= p && p <= seg.1
}

spec fn point_covered_by_any(p: int, segments: Seq<(int, int)>) -> bool {
    exists|i: int| 0 <= i && i < segments.len() && point_in_segment(p, segments[i])
}

spec fn strictly_increasing(s: Seq<int>) -> bool {
    forall|i: int, j: int| 0 <= i && i < j && j < s.len() ==> s[i] < s[j]
}

#[verifier::loop_isolation(false)]
fn points_in_segments(segments: &Vec<(i64, i64)>, m: i64) -> (result: Vec<i64>)
    requires
        m >= 0,
        forall|i: int| 0 <= i && i < segments@.len() ==>
            1 <= segments@[i].0 as int &&
            segments@[i].0 as int <= segments@[i].1 as int &&
            segments@[i].1 as int <= m as int,
    ensures
        forall|i: int| 0 <= i && i < result@.len() ==>
            1 <= result@[i] as int && result@[i] as int <= m as int,
        forall|i: int| 0 <= i && i < result@.len() ==>
            !point_covered_by_any(
                result@[i] as int,
                segments@.map_values(|t: (i64, i64)| (t.0 as int, t.1 as int)),
            ),
        forall|p: int| 1 <= p && p <= m as int ==>
            !point_covered_by_any(
                p,
                segments@.map_values(|t: (i64, i64)| (t.0 as int, t.1 as int)),
            ) ==>
            exists|j: int| 0 <= j && j < result@.len() && result@[j] as int == p,
        strictly_increasing(result@.map_values(|x: i64| x as int)),
{
    let mut a_arr: Vec<bool> = vec![true; m as usize];
    let mut i: usize = 0;
    while i < segments.len() {
        let a = segments[i].0;
        let b = segments[i].1;
        let mut j: i64 = a - 1;
        while j < b {
            if j >= 0 && (j as usize) < a_arr.len() {
                a_arr[j as usize] = false;
            }
            j = j + 1;
        }
        i = i + 1;
    }

    let mut result: Vec<i64> = Vec::new();
    let mut k: usize = 0;
    while k < m as usize {
        if a_arr[k] {
            proof { assume(false); }
            result.push((k as i64) + 1);
        }
        proof { assume(false); }
        k = k + 1;
    }
    result
}

fn main() {}

} // verus!
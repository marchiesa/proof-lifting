use vstd::prelude::*;

verus! {

spec fn in_seq(x: int, s: Seq<int>) -> bool {
    exists|i: int| 0 <= i < s.len() && #[trigger] s[i] == x
}

spec fn possible_line(line: int, stops: Seq<Seq<int>>) -> bool {
    forall|k: int| 0 <= k < stops.len() ==> in_seq(line, #[trigger] stops[k])
}

// Helper: element x appears in every stop from 0..bound
spec fn in_all_stops_up_to(x: int, stops_spec: Seq<Seq<int>>, bound: int) -> bool {
    forall|m: int| 0 <= m < bound ==> in_seq(x, #[trigger] stops_spec[m])
}

proof fn in_seq_extend(x: int, s: Seq<int>, y: int)
    requires
        in_seq(x, s),
    ensures
        in_seq(x, s.push(y)),
{
    let w = choose|w: int| 0 <= w < s.len() && s[w] == x;
    assert(s.push(y)[w] == x);
}

fn determine_line(stops: &Vec<Vec<i64>>) -> (result: Vec<i64>)
    ensures
        forall|i: int| 0 <= i < result@.len() ==> possible_line(result@[i] as int, stops@.map_values(|v: Vec<i64>| v@.map_values(|x: i64| x as int))),
        forall|k: int, j: int| 0 <= k < stops@.len() && 0 <= j < stops@[k]@.len() ==>
            (possible_line(stops@[k]@[j] as int, stops@.map_values(|v: Vec<i64>| v@.map_values(|x: i64| x as int)))
            ==> in_seq(stops@[k]@[j] as int, result@.map_values(|x: i64| x as int))),
{
    let ghost stops_spec: Seq<Seq<int>> = stops@.map_values(|v: Vec<i64>| v@.map_values(|x: i64| x as int));

    if stops.len() == 0 {
        let result: Vec<i64> = Vec::new();
        return result;
    }

    let mut result: Vec<i64> = stops[0].clone();

    // Establish initial invariant: result == stops[0], k will start at 1
    proof {
        // Soundness: every element of result is in stops_spec[0]
        // PLACEHOLDER_0: insert assertion here










        // Completeness: if x is in stops_spec[0], then x is in result
        // PLACEHOLDER_1: insert assertion here








    let mut k: usize = 1;
    while k < stops.len()
        invariant
            1 <= k <= stops.len(),
            forall|i: int| #![trigger result@[i]] 0 <= i < result@.len() ==> in_all_stops_up_to(result@[i] as int, stops_spec, k as int),
            forall|x: int| in_all_stops_up_to(x, stops_spec, k as int) ==> in_seq(x, result@.map_values(|v: i64| v as int)),
            stops_spec == stops@.map_values(|v: Vec<i64>| v@.map_values(|x: i64| x as int)),
        decreases stops.len() - k,
    {
        let mut new_result: Vec<i64> = Vec::new();
        let ghost old_result = result@;

        let mut i: usize = 0;
        while i < result.len()
            invariant
                0 <= i <= result@.len(),
                result@ == old_result,
                forall|idx: int| #![trigger new_result@[idx]] 0 <= idx < new_result@.len() ==> in_seq(new_result@[idx] as int, stops_spec[k as int]) && in_seq(new_result@[idx] as int, result@.map_values(|v: i64| v as int)),
                forall|idx: int| #![trigger result@[idx]] 0 <= idx < i ==> (in_seq(result@[idx] as int, stops_spec[k as int]) ==> in_seq(result@[idx] as int, new_result@.map_values(|v: i64| v as int))),
                stops_spec == stops@.map_values(|v: Vec<i64>| v@.map_values(|x: i64| x as int)),
                1 <= k < stops.len(),
                forall|ii: int| #![trigger result@[ii]] 0 <= ii < result@.len() ==> in_all_stops_up_to(result@[ii] as int, stops_spec, k as int),
                forall|x: int| in_all_stops_up_to(x, stops_spec, k as int) ==> in_seq(x, result@.map_values(|v: i64| v as int)),
            decreases result@.len() - i,
        {
            let mut found: bool = false;
            let mut j: usize = 0;
            while j < stops[k].len()
                invariant
                    0 <= j <= stops[k as int]@.len(),
                    found <==> exists|jp: int| 0 <= jp < j && result@[i as int] == stops[k as int]@[jp],
                    0 <= i < result@.len(),
                    1 <= k < stops.len(),
                    stops_spec == stops@.map_values(|v: Vec<i64>| v@.map_values(|x: i64| x as int)),
                decreases stops[k as int]@.len() - j,
            {
                if result[i] == stops[k][j] {
                    found = true;
                }
                j = j + 1;
            }

            if found {
                let ghost old_nr = new_result@;
                new_result.push(result[i]);

                proof {
                    // Old elements still satisfy invariants
                    assert forall|idx: int| 0 <= idx < old_nr.len() implies
                        in_seq(#[trigger] new_result@[idx] as int, stops_spec[k as int]) && in_seq(new_result@[idx] as int, result@.map_values(|v: i64| v as int))
                    by {
                        assert(new_result@[idx] == old_nr[idx]);
                    }

                    // The new element is in stops[k]
                    // PLACEHOLDER_2: insert assertion here




                    // The new element is in result
                    assert(in_seq(new_result@[old_nr.len() as int] as int, result@.map_values(|v: i64| v as int))) by {
                        assert(new_result@[old_nr.len() as int] == result@[i as int]);
                        assert(result@.map_values(|v: i64| v as int)[i as int] == result@[i as int] as int);
                    }

                    // For all idx < i+1, if result[idx] in stops[k], then in new_result
                    // PLACEHOLDER_3: insert assertion here















            }
            i = i + 1;
        }

        // Prove soundness for next iteration
        proof {
            assert forall|ii: int| 0 <= ii < new_result@.len() implies
                in_all_stops_up_to(#[trigger] new_result@[ii] as int, stops_spec, (k + 1) as int)
            by {
                assert(in_seq(new_result@[ii] as int, stops_spec[k as int]));
                assert(in_seq(new_result@[ii] as int, result@.map_values(|v: i64| v as int)));
                let ridx = choose|ridx: int| 0 <= ridx < result@.len() && result@[ridx] as int == new_result@[ii] as int;
                assert(in_all_stops_up_to(result@[ridx] as int, stops_spec, k as int));
                assert forall|m: int| 0 <= m < (k + 1) as int implies in_seq(new_result@[ii] as int, #[trigger] stops_spec[m])
                by {
                    if m == k as int {
                        assert(in_seq(new_result@[ii] as int, stops_spec[k as int]));
                    } else {
                        assert(in_seq(result@[ridx] as int, stops_spec[m]));
                    }
                }
            }

            // Prove completeness for next iteration
            // PLACEHOLDER_4: insert assertion here











        result = new_result;
        k = k + 1;
    }

    // Final proof: connect loop invariants to postconditions
    proof {
        assert forall|i: int| 0 <= i < result@.len() implies
            possible_line(result@[i] as int, stops_spec)
        by {
            assert(in_all_stops_up_to(result@[i] as int, stops_spec, stops_spec.len() as int));
        }

        // PLACEHOLDER_5: insert assertion here









    result
}

fn same_elements(a: &Vec<i64>, b: &Vec<i64>) -> (same: bool)
{
    if a.len() != b.len() {
        return false;
    }
    let mut i: usize = 0;
    while i < a.len()
        invariant
            0 <= i <= a@.len(),
        decreases a@.len() - i,
    {
        let mut found: bool = false;
        let mut j: usize = 0;
        while j < b.len()
            invariant
                0 <= j <= b@.len(),
                0 <= i < a@.len(),
            decreases b@.len() - j,
        {
            if a[i] == b[j] {
                found = true;
            }
            j = j + 1;
        }
        if !found {
            return false;
        }
        i = i + 1;
    }
    let mut i2: usize = 0;
    while i2 < b.len()
        invariant
            0 <= i2 <= b@.len(),
        decreases b@.len() - i2,
    {
        let mut found: bool = false;
        let mut j: usize = 0;
        while j < a.len()
            invariant
                0 <= j <= a@.len(),
                0 <= i2 < b@.len(),
            decreases a@.len() - j,
        {
            if b[i2] == a[j] {
                found = true;
            }
            j = j + 1;
        }
        if !found {
            return false;
        }
        i2 = i2 + 1;
    }
    return true;
}

fn main() {}

} // verus!

use vstd::prelude::*;

verus! {

spec fn cyclic_index(year: int, period: int) -> int {
    (year - 1) % period
}

spec fn gapja_name(year: int, s: Seq<Seq<char>>, t: Seq<Seq<char>>) -> Seq<char> {
    s[cyclic_index(year, s.len() as int)] + t[cyclic_index(year, t.len() as int)]
}

#[verifier::external_body]
fn string_append(s: &mut String, other: &str)
    ensures
        s@ == old(s)@ + other@,
{
    s.push_str(other)
}

#[verifier::loop_isolation(false)]
fn new_year_naming(n: i64, m: i64, s: &Vec<String>, t: &Vec<String>, queries: &Vec<i64>) -> (results: Vec<String>)
    requires
        n > 0 && m > 0,
        s@.len() == n as int,
        t@.len() == m as int,
        forall|i: int| 0 <= i < queries@.len() ==> queries@[i] >= 1,
    ensures
        results@.len() == queries@.len(),
        forall|i: int| 0 <= i < results@.len() ==>
            results@[i]@ == gapja_name(
                queries@[i] as int,
                s@.map_values(|v: String| v@),
                t@.map_values(|v: String| v@),
            ),
{
    let mut results: Vec<String> = Vec::new();
    let mut i: usize = 0;

    while i < queries.len()
        invariant
            i <= queries.len(),
            results@.len() == i as int,
            n > 0 && m > 0,
            s@.len() == n as int,
            t@.len() == m as int,
            forall|j: int| 0 <= j < queries@.len() ==> queries@[j] >= 1,
            forall|j: int| 0 <= j < i as int ==>
                results@[j]@ == gapja_name(
                    queries@[j] as int,
                    s@.map_values(|v: String| v@),
                    t@.map_values(|v: String| v@),
                ),
        decreases queries.len() - i,
    {
        let qi = queries[i];
        assert(qi >= 1);
        let x = qi - 1;

        let si = (x % n) as usize;
        let ti = (x % m) as usize;

        assert(si as int == cyclic_index(qi as int, n as int));
        assert(ti as int == cyclic_index(qi as int, m as int));

        assert(s@.map_values(|v: String| v@).len() == n as int);
        assert(t@.map_values(|v: String| v@).len() == m as int);

        // Bridge cyclic_index through map_values length to gapja_name's internal indexing
        assert(cyclic_index(qi as int, s@.map_values(|v: String| v@).len() as int) == si as int);
        assert(cyclic_index(qi as int, t@.map_values(|v: String| v@).len() as int) == ti as int);

        let mut name = s[si].clone();
        string_append(&mut name, &t[ti]);

        assert(s@.map_values(|v: String| v@)[si as int] =~= s@[si as int]@);
        assert(t@.map_values(|v: String| v@)[ti as int] =~= t@[ti as int]@);

        // Intermediate: connect name to map_values entries
        assert(name@ =~= s@.map_values(|v: String| v@)[si as int] + t@.map_values(|v: String| v@)[ti as int]);

        assert(name@ =~= gapja_name(
            qi as int,
            s@.map_values(|v: String| v@),
            t@.map_values(|v: String| v@),
        ));

        results.push(name);
        i += 1;
    }
    results
}

fn main() {}

} // verus!
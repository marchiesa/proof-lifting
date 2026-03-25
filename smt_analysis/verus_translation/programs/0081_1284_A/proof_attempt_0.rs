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
    ensures s@ == old(s)@ + other@
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
            i <= queries@.len(),
            results@.len() == i as int,
            forall|j: int| 0 <= j < i ==>
                results@[j]@ == gapja_name(
                    queries@[j] as int,
                    s@.map_values(|v: String| v@),
                    t@.map_values(|v: String| v@),
                ),
        decreases queries.len() - i
    {
        let x = queries[i] - 1;
        proof {
            assert(queries@[i as int] >= 1);
            assert(x as int == queries@[i as int] - 1);
            assert(x >= 0i64);
            assert(x as int % n as int == cyclic_index(queries@[i as int], n as int));
            assert(x as int % m as int == cyclic_index(queries@[i as int], m as int));
        }
        let si = (x % n) as usize;
        let ti = (x % m) as usize;
        proof {
            assert((x % n) as int == x as int % n as int) by(nonlinear_arith);
            assert((x % m) as int == x as int % m as int) by(nonlinear_arith);
            assert(si as int == cyclic_index(queries@[i as int], n as int));
            assert(ti as int == cyclic_index(queries@[i as int], m as int));
        }
        let mut name = s[si].clone();
        string_append(&mut name, &t[ti]);
        proof {
            let year = queries@[i as int];
            let ss = s@.map_values(|v: String| v@);
            let tt = t@.map_values(|v: String| v@);
            assert(ss.len() == n as int);
            assert(tt.len() == m as int);
            assert(ss[si as int] == s@[si as int]@);
            assert(tt[ti as int] == t@[ti as int]@);
            assert(name@ == ss[si as int] + tt[ti as int]);
            assert(si as int == cyclic_index(year, ss.len() as int));
            assert(ti as int == cyclic_index(year, tt.len() as int));
            assert(name@ == gapja_name(year, ss, tt));
        }
        results.push(name);
        i += 1;
    }
    results
}

fn main() {}

} // verus!
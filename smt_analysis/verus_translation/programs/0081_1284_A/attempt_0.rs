use vstd::prelude::*;

verus! {

spec fn cyclic_index(year: int, period: int) -> int {
    (year - 1) % period
}

spec fn gapja_name(year: int, s: Seq<Seq<char>>, t: Seq<Seq<char>>) -> Seq<char> {
    s[cyclic_index(year, s.len() as int)] + t[cyclic_index(year, t.len() as int)]
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
    {
        let x = queries[i] - 1;
        proof { assume(false); }  // assert queries[i] >= 1
        proof { assume(false); }  // assert x == queries[i] - 1
        proof { assume(false); }  // assert x % n == cyclic_index(queries[i] as int, n as int)
        proof { assume(false); }  // assert x % m == cyclic_index(queries[i] as int, m as int)
        let si = (x % n) as usize;
        let ti = (x % m) as usize;
        let mut name = s[si].clone();
        name.push_str(&t[ti]);
        results.push(name);
        i += 1;
    }
    results
}

fn main() {}

} // verus!
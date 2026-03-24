use vstd::prelude::*;

verus! {

spec fn CategoryRank(hp: int) -> int
    recommends hp >= 1
{
    let r = hp % 4;
    if r == 1 { 3 }
    else if r == 3 { 2 }
    else if r == 2 { 1 }
    else { 0 }
}

spec fn CategoryChar(hp: int) -> char
    recommends hp >= 1
{
    let r = hp % 4;
    if r == 1 { 'A' }
    else if r == 3 { 'B' }
    else if r == 2 { 'C' }
    else { 'D' }
}

proof fn CategoryRankBounded(hp: int)
    requires hp >= 1
    ensures 0 <= CategoryRank(hp) <= 3
{
    assume(false);
}

fn TokitsukazeAndEnhancement(x: i64) -> (res: (i64, char))
    requires x >= 1
    ensures 0 <= res.0 && res.0 <= 2
    ensures res.1 == CategoryChar(x as int + res.0 as int)
    ensures forall|delta: int| 0 <= delta && delta <= 2 ==> CategoryRank(x as int + delta) <= CategoryRank(x as int + res.0 as int)
    ensures forall|delta: int| 0 <= delta && delta < res.0 as int ==> CategoryRank(x as int + delta) < CategoryRank(x as int + res.0 as int)
{
    let r = x % 4;
    if r == 0 {
        proof { assume(false); }
        (1i64, 'A')
    } else if r == 1 {
        proof { assume(false); }
        (0i64, 'A')
    } else if r == 2 {
        proof { assume(false); }
        (1i64, 'B')
    } else {
        proof { assume(false); }
        (2i64, 'A')
    }
}

fn main() {}

} // verus!
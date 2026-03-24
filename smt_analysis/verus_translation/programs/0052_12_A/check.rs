use vstd::prelude::*;

verus! {

spec fn valid_grid(grid: Seq<Seq<char>>) -> bool {
    grid.len() == 3 && forall|i: int| 0 <= i < 3 ==> grid[i].len() == 3
}

spec fn symmetric_about_center(grid: Seq<Seq<char>>) -> bool
    recommends valid_grid(grid)
{
    forall|i: int, j: int| (0 <= i < 3 && 0 <= j < 3) ==>
        (grid[i][j] == 'X' ==> grid[2 - i][2 - j] == 'X')
}

spec fn checked_so_far(grid: Seq<Seq<char>>, row: int, col: int) -> bool
    recommends valid_grid(grid)
    recommends 0 <= row <= 3
    recommends 0 <= col <= 3
{
    forall|i: int, j: int| (0 <= i < row && 0 <= j < 3) ==>
        (grid[i][j] == 'X' ==> grid[2 - i][2 - j] == 'X')
}

spec fn checked_row(grid: Seq<Seq<char>>, row: int, col: int) -> bool
    recommends valid_grid(grid)
    recommends 0 <= row < 3
    recommends 0 <= col <= 3
{
    forall|j: int| (0 <= j < col) ==>
        (grid[row][j] == 'X' ==> grid[2 - row][2 - j] == 'X')
}

#[verifier::loop_isolation(false)]
fn super_agent(grid: &Vec<Vec<char>>) -> (symmetric: bool)
    requires valid_grid(grid@.map_values(|v: Vec<char>| v@))
    ensures symmetric == symmetric_about_center(grid@.map_values(|v: Vec<char>| v@))
{
    let mut bad = false;
    let mut i: usize = 0;
    while i < 3 {
        let mut j: usize = 0;
        while j < 3 {
            if grid[i][j] == 'X' && grid[2 - i][2 - j] != 'X' {
                bad = true;
            }
            j = j + 1;
        }
        i = i + 1;
    }
    !bad
}

fn main() {}

}